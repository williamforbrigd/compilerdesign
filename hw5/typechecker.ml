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
  match (t1, t2) with
  |(TInt, TInt) -> true 
  |(TBool, TBool) -> true
  |(TRef rty1, TRef rty2) -> subtype_ref c rty1 rty2 
  |(TNullRef rty1, TNullRef rty2)->subtype_ref c rty1 rty2
  |(TNullRef rty1, TRef rty2)->false
  |(TRef rty1, TNullRef rty2)->subtype_ref c rty1 rty2

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
    match (t1, t2) with
    |(RString, RString) -> true 
    |(RStruct id1, RStruct id2) -> 
      let val1, val2 = Tctxt.lookup_struct id1 c, Tctxt.lookup_struct id2 c in
      begin match (val1, val2) with
      |(lst1, lst2) -> true
      |(_,_) -> false
      end
    |(RArray ty1, RArray ty2)->true
    |(RFun(lst1, ret_ty1), RFun(lst2, ret_ty2))->
      let rec subtype_ref_aux c lst1 lst2 acc =  
        begin match (lst1, lst2) with
        |([x], [y])-> subtype c y x  && subtype_ret c ret_ty1 ret_ty2
        |((h1::tl1), (h2::tl2))->
          if subtype c h2 h1 then subtype_ref_aux c lst1 lst2 acc else false
        |(_,_)->false
        end
      in subtype_ref_aux c lst1 lst2 false

  (*Decides whether H |-r rt1 <: rt2*)
  and subtype_ret (c: Tctxt.t) (ret_ty1: Ast.ret_ty) (ret_ty2: Ast.ret_ty) : bool = 
      match (ret_ty1, ret_ty2) with
      |(RetVoid, RetVoid)->true
      |(RetVal ty1, RetVal ty2)-> subtype c ty1 ty2

    


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
  |TRef rty ->typecheck_rty l tc rty 
  |TNullRef rty1->()
  |_->type_error l "Not a valid type"

and typecheck_rty (l: 'a Ast.node) (tc : Tctxt.t) (rty : Ast.rty) : unit = 
  match rty with
  |RString->()
  |RArray ty -> typecheck_ty l tc ty
  |RStruct id -> 
    let val1 = Tctxt.lookup_struct id tc in
    begin match val1 with
    |lst -> ()
    |_ -> type_error l "Not a valid struct in the context."
    end
  |RFun(types, ret_ty)->
    let res = List.fold_left (fun tmp ty ->
      if typecheck_ty l tc ty == () then () else type_error l "One of the types in the function are not valid" 
      ) () types
    in 
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
  |CNull rty -> 
    if typecheck_rty l c rty == () then TNullRef rty else type_error l "TYP_NULL not valid" 
  |CBool b -> TBool
  |CInt i -> TInt
  |CStr s -> TRef RString 
  |Id id -> 
    begin match (Tctxt.lookup_local_option id c, Tctxt.lookup_global_option id c) with
    |(Some x,_)->x
    |(None, Some x)->x
    |_->type_error l "TYP_LOCAL or TYP_GLOBAL not valid"
    end

  |CArr(ty, exps) -> 
    let res = List.iter (fun exp -> 
      let sub = typecheck_exp c e in
      let is_sub = subtype c sub ty in
      if is_sub then typecheck_ty l c sub else type_error l "TYP_CARR Not a subtype"
      ) exps
    in 
    let res2 = typecheck_ty l c ty in
    if res == () && res2 == () then ty else type_error l "TYP_CARR not valid"
  |_-> type_error l "Failed to typecheck the expression"

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
  begin match s.elt with
  |Assn(lhs, exp) -> 
    (*Check that the lhs expression is a local or that it does not have a global id*)
    begin match (typecheck_exp tc lhs, typecheck_exp tc exp) with
    (*lhs = exp*)
    |(t, t') -> if (subtype tc t' t) then (tc, false) else type_error s "TYP_ASSN not valid"
    end
  end

(*TODO: add helper function for typecheck_block *)
(*TODO: wtf shall this return*)
let typecheck_block (tc : Tctxt.t) (b : Ast.block) (ret : ret_ty) : Tctxt.t * ret_ty = 
  (* List.fold_left (fun (bl, ret) -> 
    ) (tc, ret) b
 *)
  (**TODO: check that the last statement has the right return type *)
  let rec typecheck_block_aux tc b ret acc = 
    begin match b with
    |[] -> acc
    |[s] -> 
      begin match (typecheck_stmt tc s ret) with
      |(ctxt,will_ret)-> if will_ret then (ctxt, ret) else type_error s ""
      end
    end
  in typecheck_block_aux tc b ret (tc, ret) 

(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

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
let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  (*Add all the arguments to the local context*)
  List.map(fun arg ->
    begin match (Tctxt.lookup_local_option (snd arg) tc) with
    |Some x -> failwith "Arg is already in the local context"
    |None -> Tctxt.add_local tc (snd arg) (fst arg)
    end
    ) f.args;
  (**Typecheck the body of the function *)
  failwith "typecheck_fdecl not finished yet"

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
  let c = Tctxt.empty in
  let rec create_struct_ctxt_aux p acc = 
    begin match p with
  | [] -> acc
  | (h::tl) -> 
    begin match h with
    | Gtdecl t ->
      begin match t.elt with
      | (id, fields) -> 
        begin match (Tctxt.lookup_struct_option id c) with
        | Some s -> failwith "Cannot add struct if it already exists"
        | None -> 
          Tctxt.add_struct c id fields;
          create_struct_ctxt_aux tl acc
        end
      end
    end
  end
  in create_struct_ctxt_aux p c

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left(fun c el -> 
    begin match el with
    |Gfdecl f ->
      begin match f.elt with
      |fdecl -> 
        List.fold_left(fun c arg -> 
          begin match (Tctxt.lookup_local_option (snd arg) tc) with
          |Some x -> failwith "is already in the context"
          |None -> Tctxt.add_local c (snd arg) (fst arg)
          end
          ) c fdecl.args
        end
    end
    ) tc p

(*TODO: is this the right way to create the global context*)
let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  List.fold_left (fun c el -> 
    begin match el with
    |Gvdecl g ->
      begin match g.elt with
      |gdecl ->
        begin match (Tctxt.lookup_global_option gdecl.name c) with
        |Some x -> failwith "Global declaration already in the context"
        |None -> Tctxt.add_global c gdecl.name (typecheck_exp c gdecl.init)
        end
      end
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
