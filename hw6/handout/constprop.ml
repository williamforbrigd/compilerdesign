open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"


  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate
   to integer constants *)
type fact = SymConst.t UidM.t

let fact_to_string : fact -> string =
  UidM.to_string (fun _ v -> SymConst.to_string v)

let f1 (a:'a) : 'a = SymConst.NonConst
(* let f2 (a:'a) : 'a =  *)
let f3 (a:'a) : 'a = SymConst.UndefConst

let get_value_bop bop c1 c2 =
  begin match bop with
  | Add -> Int64.add c1 c2
  | Sub -> Int64.sub c1 c2
  | Mul -> Int64.mul c1 c2
  | Shl -> Int64.shift_left c1 (Int64.to_int c2)
  | Lshr -> Int64.shift_right_logical c1 (Int64.to_int c2)
  | Ashr -> Int64.shift_right c1 (Int64.to_int c2)
  | And -> Int64.logand c1 c2
  | Or -> Int64.logor c1 c2
  | Xor -> Int64.logxor c1 c2
  |_ -> failwith "not found"
 end

let get_value_cnd cnd c1 c2 =
  let eq = Int64.equal c1 c2 in
  let comp = Int64.compare c1 c2 in
  begin match cnd with
  | Eq -> if eq then 1L else 0L
  | Ne -> if eq then 0L else 1L
  | Slt -> if comp < 0 then 1L else 0L
  | Sle -> if comp < 0 || comp == 0 then 1L else 0L
  | Sgt -> if comp > 0 then 1L else 0L
  | Sge -> if comp > 0 || comp == 0 then 1L else 0L
  | _ -> failwith "not found"
  end


(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)


let insn_flow (u,i:uid * insn) (d:fact) : fact =
  let t1 = SymConst.NonConst in
  let t2 x = SymConst.Const x in
  let t3 = SymConst.UndefConst in

  begin match i with
  |Binop(bop, ty, op1, op2) ->
    begin match op1, op2 with
    | Const c1, Const c2 ->
      let value = get_value_bop bop c1 c2 in
      UidM.update_or t1 (fun x -> t2 (value)) u d
    | Id uid1, Id uid2 ->
      let find1 = UidM.find_or t1 d uid1 in
      let find2 = UidM.find_or t1 d uid2 in
      begin match find1, find2 with
      | SymConst.Const c1, SymConst.Const c2 ->
        let value = get_value_bop bop c1 c2 in
        UidM.update_or t1 (fun x -> t2 value) u d
      | _,_ -> UidM.update_or t1 f1 u d
      end
    |Const c1, Id uid ->
      let find = UidM.find_or t1 d uid in
      begin match find with
      |SymConst.Const c2 ->
        let value = get_value_bop bop c1 c2 in
        UidM.update_or t1 (fun x -> t2 value ) u d
      |_ -> UidM.update_or t1 f1 u d
      end
    |Id uid, Const c2 ->
      let find = UidM.find_or t1 d uid in
      begin match find with
      |SymConst.Const c1 ->
        let value = get_value_bop bop c1 c2 in
        UidM.update_or t1 (fun x -> t2 value ) u d
      |_ -> UidM.update_or t1 f1 u d
      end
    | _,_ -> UidM.update_or t1 f1 u d
    end

  |Icmp(cnd, top, op1, op2) ->
    begin match op1, op2 with
    |Const c1, Const c2 ->
      let value = get_value_cnd cnd c1 c2 in
      UidM.update_or t1 (fun x -> t2 value) u d
    | Id uid1, Id uid2 ->
      let find1 = UidM.find_or t1 d uid1 in
      let find2 = UidM.find_or t1 d uid2 in
      begin match find1, find2 with
      | SymConst.Const c1, SymConst.Const c2 ->
        let value = get_value_cnd cnd c1 c2 in
        UidM.update_or t1 (fun x -> t2 value) u d
      | _,_ -> UidM.update_or t1 f1 u d
      end
    |Const c1, Id uid ->
      let find = UidM.find_or t1 d uid in
      begin match find with
      |SymConst.Const c2 ->
        let value = get_value_cnd cnd c1 c2 in
        UidM.update_or t1 (fun x -> t2 value ) u d
      |_ -> UidM.update_or t1 f1 u d
      end
    |Id uid, Const c2 ->
      let find = UidM.find_or t1 d uid in
      begin match find with
      |SymConst.Const c1 ->
        let value = get_value_cnd cnd c1 c2 in
        UidM.update_or t1 (fun x -> t2 value ) u d
      |_ -> UidM.update_or t1 f1 u d
      end
    |_,_ -> UidM.update_or t1 f1 u d
    end

  |Store(ty, op1, op2) -> UidM.update_or t1 f3 u d

  |Call(ty, op, lst) ->
    begin match ty with
    |Void -> UidM.update_or t3 f3 u d
    |_ -> UidM.update_or t1 f1 u d
    end

  | _ -> UidM.update_or t1 f1 u d
  end

(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow

    let normalize : fact -> fact =
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  =
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let combine (ds:fact list) : fact =
      ds |> List.fold_left (fun acc elt ->
        UidM.merge (fun key x0 y0 ->
          begin match x0, y0 with
          |Some x, Some y -> Some x
          |Some x, None-> Some x
          |None, Some y -> Some y
          end
          ) acc elt
        ) UidM.empty
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg

(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper
   functions.                                                                 *)
let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in

  let t1 = SymConst.NonConst in
  let t2 x = SymConst.Const x in
  let t3 = SymConst.UndefConst in

  let cp_op op m : operand = 
    begin match op with
    | Id uid -> 
        begin match UidM.find_or t1 m uid with
        | SymConst.Const c -> Const c 
        | _ -> op
        end
    | _ -> op
    end 
  in

  let cp_ops op1 op2 m : (operand * operand) = 
    begin match op1, op2 with
    | Id uid1, Id uid2 -> 
      begin match (UidM.find_or t1 m uid1, UidM.find_or t1 m uid2) with
      | SymConst.Const c1, SymConst.Const c2 -> Const c1, Const c2
      | SymConst.Const c, _ -> Const c, op2
      | _, SymConst.Const c -> op1, Const c
      | _,_ -> op1,op2
      end
    |Id uid, _ ->
      begin match (UidM.find_or t1 m uid) with
      | SymConst.Const c -> Const c, op2 
      | _ -> op1, op2 
      end
    |_, Id uid -> 
      begin match (UidM.find_or t1 m uid) with
      | SymConst.Const c -> op1, Const c 
      | _ -> op1, op2 
      end
    | _,_ -> op1, op2
    end
  in

  let cp_insn (i : Ll.insn) (m : Fact.t) (u : Ll.uid) : Ll.insn = 
    match i with
    | Binop(bop, ty, op1, op2) ->
      let op1', op2' = cp_ops op1 op2 m in
      Binop(bop, ty, op1', op2')

    | Load(ty, op) -> 
      let op' = cp_op op m in
      Load(ty, op')

    | Store(ty, op1, op2) -> 
      let op1', op2' = cp_ops op1 op2 m in
      Store(ty, op1', op2')
    
    | Icmp(cnd, ty, op1, op2) -> 
      let op1', op2' = cp_ops op1 op2 m in
      Icmp(cnd, ty, op1', op2')

    | Call(ty, op, args) -> 
      let op' = cp_op op m in
      let new_args = List.map(fun arg -> 
        let t, op1 = arg in
        let op1' = cp_op op1 m in
        t, op1'
        ) args in
      Call(ty, op', new_args)

    | Bitcast(ty1, op, ty2) -> 
      let op' = cp_op op m in
      Bitcast(ty1, op', ty2)

    | Gep(ty, op1, ops) -> 
      (*TODO: constant propagate all the ops list or*)
      let op1' = cp_op op1 m in
      Gep(ty, op1', ops)

    | _ -> i (**the other instructions does not have an operand, so just return the same i*)
  in

  let cp_term term m = 
    match term with
    | Ret(ty, opt) -> 
      begin match opt with
      | Some op -> 
        begin match op with
        | Id uid -> 
          begin match (UidM.find_or t1 m uid) with
          | SymConst.Const c -> Ret(ty, Some(Const c))
          | _ -> term
          end
        | _ -> term
        end
      | None -> term
      end
    | Cbr(op, lbl1, lbl2) ->
      begin match op with
      | Id uid -> 
        begin match (UidM.find_or t1 m uid) with
        | SymConst.Const c -> Cbr(Const c, lbl1, lbl2)
        | _ -> term
        end
      | _ -> term
      end
    | Br lbl -> term
  in


  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    (* print_endline (Llutil.string_of_block b); *)
    (*Ll.uid -> Fact.t*)
    (* print_endline (cfg); *)
    (* failwith "Constprop.cp_block unimplemented" *)
    let new_insns = List.map(fun insn ->
      let u,i = insn in
      let m = cb u in
      let new_i = cp_insn i m u in
      (* let str = begin match i with
      | Binop(bop, ty, op1, op2) -> "old: " ^ Llutil.string_of_insn i ^ " new: " ^ Llutil.string_of_insn new_i
      | _ -> "nop"
      end in
      print_endline str; *)
      u,new_i
      ) b.insns in
    let u_term, term = b.term in
    let m = cb u_term in
    let new_term = cp_term term m in
    let new_b = {insns = new_insns; term = (u_term, new_term)} in
    let new_m = LblM.update_or b (fun x -> new_b) l cfg.blocks in
    {blocks = new_m; preds = cfg.preds; ret_ty = cfg.ret_ty; args = cfg.args}
  in
    

  LblS.fold cp_block (Cfg.nodes cfg) cfg
