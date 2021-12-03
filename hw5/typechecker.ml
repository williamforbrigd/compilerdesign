open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1, t2 with
  |TInt, TInt -> true 
  |TBool, TBool -> true
  |TNullRef rty1, TNullRef rty2
  |TRef rty1, TRef rty2
  |TRef rty1, TNullRef rty2 -> subtype_ref c rty1 rty2
  |_,_ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
    match (t1, t2) with
    |(RString, RString) -> true 
    |(RArray ty1, RArray ty2)->true
    |(RStruct id1, RStruct id2) -> 
      begin match (Tctxt.lookup_struct_option id1 c, Tctxt.lookup_struct_option id2 c) with
      | Some lst1, Some lst2 -> true
      | _,_ -> false
      end
    |(RFun(lst1, ret_ty1), RFun(lst2, ret_ty2))->
      let all_is_sub = List.for_all2 (fun el1 el2 ->
        subtype c el2 el1
        ) lst1 lst2
      in 
      all_is_sub && subtype_ret c ret_ty1 ret_ty2
      (**Alternativ *)
      (* let (_ , is_sub) = List.fold_left (fun (i, is_sub) el1 ->
        if subtype c (List.nth lst2 i) el1 then (i+1, true) else (i+1, false)
        ) (0, false) lst1
      *)
      (**Alternativ *)
      (* let (_, is_sub) = List.fold_left (fun (i, is_sub) el1 -> 
        if subtype c (List.nth lst2 i) el1 then (i-1, true) else (i-1, false)
        ) (List.length lst2, false) (List.rev lst1) *)

      (* let (_, is_sub) = List.fold_right (fun el1 (i, is_sub) -> 
        if subtype c (List.nth lst2 i) el1 then (i-1, true) else (i-1, false)
        ) lst1 (List.length lst2, false)
      in is_sub && subtype_ret c ret_ty1 ret_ty2
       *)
      (*Alternativ*)
      (* let arr = List.mapi (fun lst1_pos el1 -> 
        if subtype c (List.nth lst2 lst1_pos) el1 then lst1_pos else 0
      ) lst1
      in 
      if (List.nth arr (List.length arr-1) == List.length lst1 - 1) then subtype_ret c ret_ty1 ret_ty2 else false *)
    |_,_ -> false

  (*Decides whether H |-r rt1 <: rt2*)
  and subtype_ret (c: Tctxt.t) (ret_ty1: Ast.ret_ty) (ret_ty2: Ast.ret_ty) : bool = 
      match (ret_ty1, ret_ty2) with
      |(RetVoid, RetVoid)->true
      |(RetVal ty1, RetVal ty2)-> subtype c ty1 ty2
      |(_,_) -> false

    


(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is 

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  |TInt->()
  |TBool->()
  |TRef rty | TNullRef rty -> typecheck_rty l tc rty
  |_->type_error l "Not a valid type"

and typecheck_rty (l: 'a Ast.node) (tc : Tctxt.t) (rty : Ast.rty) : unit = 
  match rty with
  |RString->()
  |RArray ty -> typecheck_ty l tc ty
  |RStruct id -> 
    begin match (Tctxt.lookup_struct_option id tc) with
    | Some x -> ()
    | None -> type_error l "WF_REFTOKOKSTRUCT not valid"
    end
  |RFun(types, ret_ty)->
    let res = List.fold_left (fun tmp ty -> typecheck_ty l tc ty) () types in 
    typecheck_ret_ty l tc ret_ty 

and typecheck_ret_ty (l : 'a Ast.node) (tc : Tctxt.t) (ret_ty : Ast.ret_ty) : unit = 
  match ret_ty with
  |RetVoid->()
  |RetVal ty -> typecheck_ty l tc ty

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  let l = no_loc () in 
  match e.elt with
  |CNull rty -> TNullRef rty
  (* |CNull rty ->  *)
    (* if typecheck_rty l c rty == () then TNullRef rty else type_error l "TYP_NULL not valid"  *)
  |CBool b -> TBool
  |CInt i -> TInt
  |CStr s -> TRef RString 
  |Id id -> 
    begin match (Tctxt.lookup_local_option id c, Tctxt.lookup_global_option id c) with
    |(Some x,_)->x
    |(None, Some x)->x
    |_,_->type_error l "TYP_LOCAL or TYP_GLOBAL not valid"
    end

  (*Should the list here be sorted? *)
  |CArr(ty, exps) -> 
    let is_valid = List.fold_left (fun is_valid exp -> 
      let ty_checked = typecheck_exp c exp in
      subtype c ty_checked ty
      ) false (List.sort compare exps)
    in 
    if is_valid then TRef(RArray ty) else type_error l "TYP_CARR not a valid type"

  |NewArr(ty, exp1, id, exp2) -> 
    let is_int = begin match (typecheck_exp c exp1) with
    |TInt->true
    |_->type_error l "TYP_NEWARR Length is not an integer"; false
    end in
    let is_global = begin match (Tctxt.lookup_local_option id c, Tctxt.lookup_global_option id c) with
    |(Some x, _) -> type_error l "TYP_NEWARR the id cannot be a local"; false 
    |(None, Some x)-> true
    |(_,_)-> type_error l "TYP_NEWARR the id is not global"; false
    end in
    let is_sub = begin match (typecheck_exp c exp2) with
    |t'-> subtype c t' ty
    |_->type_error l "TYP_NEWARR is not subtype"
    end in
    if is_int && is_global && is_sub then TRef(RArray ty) else type_error l "TY_NEWARR not valid"
  
  |Index(n1, n2) -> 
    begin match (typecheck_exp c n1, typecheck_exp c n2) with
    | (TRef(RArray t), TInt) -> t
    | (_,_) -> type_error l "TYP_INDEX not valid"
    end
  
  |Length exp -> 
      begin match (typecheck_exp c exp) with
      | TRef(RArray t) -> TInt
      | _ -> type_error l "TYP_LENGTH not valid"
      end

  |CStruct(id, expsi) -> 
    begin match (Tctxt.lookup_struct_option id c) with
    |Some fields ->
      let all_is_sub = List.for_all2 (fun field exp ->
        let t' = typecheck_exp c (snd exp) in 
        subtype c t' field.ftyp
        ) fields expsi
      in 
      if all_is_sub then TRef(RStruct id) else type_error e "TYP_STRUCTEX not all are subtypes"
    |None -> type_error e "TYP_STRUCTEX The struct has to already exist"
    end
  
  |Proj(exp, id) ->
    begin match typecheck_exp c exp with
    |TRef(RStruct struct_id) ->
      begin match Tctxt.lookup_struct_option struct_id c with
      |Some fields ->
        let does_exist = List.exists (fun field -> 
          id = field.fieldName
          ) fields
        in
        if does_exist then Tctxt.lookup id c else type_error e "TYP_FIELD cannot find the id in the struct"
      |None -> type_error e "TYP_FIELD cannot find the struct"
      end
    |_ -> type_error e "TYP_FIELD the exp has to be a struct"
    end

  |Call(exp, exps) -> 
    begin match typecheck_exp c exp with
    |TRef(RFun(types, ret_ty)) ->
      begin match ret_ty with
      |RetVal ty -> 
        let all_is_sub = List.for_all2 (fun exp t ->
          let t' = typecheck_exp c exp in
          subtype c t' t
          ) exps types
        in
        if all_is_sub then ty else type_error e "TYP_CALL all need to be sub"
      |_ -> type_error e "TYP_CALL the function need a return type"
      end
    |_-> type_error e "TYP_CALL the expression has to evaluate to a function for it to be called"
    end

  |Bop(binop, exp1, exp2) ->
    begin match (typecheck_exp c exp1, typecheck_exp c exp2) with
    |t1, t2 ->
      let t1', t2', ret_ty = typ_of_binop binop in
      if t1 == t1' && t2 == t2' then ret_ty else type_error e "TYP_BINOP the types does not match"
    |_->type_error e "TYP_BINOP the expressions does not evaluate to types"
    end

  |Uop(unop, exp) ->
    let t, ret_ty = typ_of_unop unop in
    let t' = typecheck_exp c exp in
    if t == t' then ret_ty else type_error e "TYP_UOP the types does not match"


(*Variable declarations
typecheck them and add them to the local context if they don't exist
*)
(*When you typechekc the vdecl should you return the type as well as the context?*)
(*TODO: lets just return this for now*)
let typecheck_vdecl (tc : Tctxt.t) (vdecl : Ast.id * Ast.exp Ast.node) : Tctxt.t = 
  begin match Tctxt.lookup_option (fst vdecl) tc with
  |Some x -> failwith "TYP_DECL not valid. Already in the context"
  |None -> 
    let t = typecheck_exp tc (snd vdecl) in
    Tctxt.add_local tc (fst vdecl) t
    (* (fst vdecl), t *)
  end

let typecheck_vdecls (tc : Tctxt.t) (vdecls : (Ast.id * Ast.exp Ast.node) list ) : Tctxt.t =
  List.fold_left (fun tc vdecl -> 
    typecheck_vdecl tc vdecl 
    ) tc vdecls


(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statment typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entier conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  match s.elt with
  |Assn(lhs, exp) -> 
    (*Check that the lhs expression is a local or that it does not have a global id*)
    begin match (typecheck_exp tc lhs, typecheck_exp tc exp) with
    (*lhs = exp*)
    |(t, t') -> if (subtype tc t' t) then (tc, false) else type_error s "TYP_ASSN not valid"
    end

  |Decl vdecl -> 
    typecheck_vdecl tc vdecl, false 

  |Ret(opt) -> 
    begin match opt with
    |Some exp ->
      begin match to_ret with
      |RetVal ty -> 
        begin match typecheck_exp tc exp with
        |t' -> if subtype tc t' ty then tc, true else type_error s "TYP_RETT not a subtype"
        |_ -> type_error s "TYP_RETT not valid"
        end
      |RetVoid -> type_error s "TYP_RETT should not return void"
      end
    |None ->
      begin match to_ret with
      |RetVoid -> tc, true
      |_ -> type_error s "TYP_RETVOID not valid"
      end
    end

  |SCall(exp, exps) -> 
    begin match (typecheck_exp tc exp) with
    |TRef(rty) | TNullRef rty -> 
      begin match rty with
      |RFun(types, ret_ty) -> 
        begin match ret_ty with
        |RetVoid -> 
          let all_is_sub = List.for_all2 (fun expi t -> 
            let t' = typecheck_exp tc expi in 
            if subtype tc t' t then true else false
            ) exps types
          in 
          if all_is_sub then tc, false else type_error s "TYP_SCALL not all subtypes"
        |_->type_error s "TYP_SCALL expression does not return void"
        end
      end
    end

  |If(exp, b1, b2) -> 
    begin match (typecheck_exp tc exp) with
    |TBool ->
      let (_, r1) = typecheck_stmts tc b1 to_ret in
      let (_, r2) = typecheck_stmts tc b2 to_ret in
      tc, r1 && r2
    (*TODO: do you have to check TNullRef as well*)
    (* |TNullRef rty ->  *)
    |_-> type_error s "TYP_IF or TYP_IFQ not valid"
    end

  |While(exp, stmts) -> 
    begin match typecheck_exp tc exp with
    |TBool ->
      typecheck_stmts tc stmts to_ret
    |_ -> type_error s "TYP_WHILE the expression is not a boolean"
    end

  |For(vdecls, exp_opt, stmt_opt, stmts) -> 
    typecheck_vdecls tc vdecls;
    typecheck_stmts tc stmts to_ret;
    begin match (exp_opt, stmt_opt) with
    |Some exp, Some stmt ->
      begin match (typecheck_exp tc exp, typecheck_stmt tc stmt to_ret) with
      |(TBool, (c, will_ret)) -> 
        if will_ret then type_error stmt "TYP_FOR statement has to not return" else tc, false
      end
    |_, Some stmt -> type_error s "TYP_FOR none or both has to be present"
    |Some exp, _ -> type_error s "TYP_FOR none or both has to be present"
    end
  |_ -> type_error s "Not a valid statement"

and typecheck_stmts (tc : Tctxt.t) (stmts: Ast.stmt Ast.node list) (to_ret : ret_ty) : Tctxt.t * bool = 
List.fold_left (fun (c, will_ret) stmt -> 
    typecheck_stmt tc stmt to_ret
    ) (tc, false) stmts

(* let (_,num_false,last_ret,c) = List.fold_left (fun (i, num_false, last_ret, c) stmt -> 
  if i == ((List.length stmts) - 1) then 
    let con,ret_val = typecheck_stmt tc stmt to_ret in
    (i+1, num_false, ret_val, con)
  else
    let con, ret_val = typecheck_stmt tc stmt to_ret in
    if ret_val == false then (i+1, num_false+1, false, con) else (i+1, num_false, false, con)
  ) (0, 0, false, tc) stmts
in
if num_false == List.length stmts-2 then c,last_ret else failwith "TYP_STMTS all the statements before the last one must be false" *)

 let typecheck_block (tc : Tctxt.t) (b : Ast.block) (ret : ret_ty) : unit = 
  let c, will_ret = typecheck_stmts tc b ret in
  if will_ret then () else type_error (no_loc ()) "The block has to return"



(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let rec check_dups2 (types: (Ast.id * Ast.ty) list) = 
  match types with
  | [] -> false
  | h :: t -> (List.exists (fun x -> fst x = fst h) t) || check_dups2 t

let rec check_dups_struct (types: (Ast.id * Ast.field list) list) = 
  match types with
  | [] -> false
  | h :: t -> (List.exists (fun x -> fst x = fst h) t) || check_dups_struct t



let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)

let rec check_dups_args (args : (Ast.ty * Ast.id) list) : bool = 
  begin match args with
  |[] -> false  
  |h::tl -> (List.exists (fun arg -> snd h == snd arg) args) ||check_dups_args tl
  end

let typecheck_fdecl (tc : Tctxt.t) (f: Ast.fdecl) (l : 'a Ast.node) : unit =
  (*Add all the arguments to the local context*)
  (*TODO: check if the fields are distinct using the function over *)
  (* if check_dups_args f.args then failwith "there are duplicate fields in the arguments"
  else (
    List.map(fun arg ->
      begin match (Tctxt.lookup_local_option (snd arg) tc) with
      |Some x -> failwith "Arg is already in the local context"
      |None -> Tctxt.add_local tc (snd arg) (fst arg)
      end
      ) f.args
  ); *)
  (* typecheck_block tc f.body f.frtyp *)
  let c, will_ret = typecheck_stmts tc f.body f.frtyp in 
  if will_ret then () else failwith "Will not return"

(* let typecheck_block (tc : Tctxt.t) (b : Ast.block) (l : 'a Ast.node) : unit =   *)
(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'S'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'F' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let tc = Tctxt.empty in
  List.fold_left (fun c el -> 
    begin match el with
    |Gvdecl g -> c
    |Gfdecl f -> c
    |Gtdecl t ->
      begin match (lookup_struct_option (fst t.elt) c) with
      |Some x -> failwith "Cannot add struct if already exists"
      |None -> 
        if check_dups (snd t.elt) then failwith "Cannot add struct because there are duplicate fields"
        else Tctxt.add_struct c (fst t.elt) (snd t.elt)
      end
    |_-> c
    end
    ) tc p

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left(fun c el -> 
    begin match el with
    |Gtdecl t -> c
    |Gvdecl g -> c
    |Gfdecl f ->
      List.fold_left(fun c arg -> 
        begin match (Tctxt.lookup_global_option(snd arg) tc) with
        |Some x -> failwith "Function argument is already in the context"
        |None -> Tctxt.add_local c (snd arg) (fst arg)
        end
        ) c f.elt.args
    |_ -> c
    end
    ) tc p

(*TODO: is this the right way to create the global context*)
let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left (fun c el -> 
    begin match el with
    |Gtdecl t -> c
    |Gfdecl f -> c
    |Gvdecl g ->
      begin match g.elt with
      |gdecl ->
        begin match (Tctxt.lookup_global_option gdecl.name c) with
        |Some x -> failwith "Global declaration already in the context"
        |None -> Tctxt.add_global c gdecl.name (typecheck_exp c gdecl.init)
        end
      end
    |_ -> c
    end
    ) tc p


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
