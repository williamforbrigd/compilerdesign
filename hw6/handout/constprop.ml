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


(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)

(* let get_value bop c1 c2 = 
  begin match bop with
  | Add -> Int64.add c1 c2
  | Sub -> Int64.sub c1 c2
  | Mul -> Int64.mul c1 c2
  |_ -> UidM.empty
  end *)

let insn_flow (u,i:uid * insn) (d:fact) : fact =
  let t1 = SymConst.NonConst in
  let t2 x = SymConst.Const x in
  let t3 = SymConst.UndefConst in
  begin match i with
  
  (**Binop if one if the operands is a UndefConst *)
  |Binop(bop, ty, op1, op2) -> 
    begin match op1, op2 with
    |Id uid1, Id uid2 -> 
      let find1 = UidM.find_or t1 d uid1 in
      let find2 = UidM.find_or t1 d uid2 in
      begin match find1,find2 with 
      |SymConst.UndefConst, SymConst.UndefConst-> UidM.update_or t1 f3 u d
      |_, SymConst.UndefConst-> UidM.update_or t1 f3 u d
      |SymConst.UndefConst, _ -> UidM.update_or t1 f3 u d
      |_,_ -> UidM.update_or t1 f1 u d
      end
    |Id uid, _ -> 
      let find = UidM.find_or t1 d uid in
      begin match find with
      |SymConst.UndefConst-> UidM.update_or t3 f3 u d
      | _ -> UidM.update_or t1 f1 u d
      end
    | _, Id uid -> 
      let find = UidM.find_or t1 d uid in
      begin match find with
      |SymConst.UndefConst-> UidM.update_or t3 f3 u d
      | _ -> UidM.update_or t1 f1 u d
      end
    | _,_ -> UidM.update_or t1 f1 u d
    end
  
  |Store(ty, op1, op2) -> UidM.update_or t1 f3 u d 
  |Call(ty, op, lst) -> 
    begin match ty with
    |Void -> UidM.update_or t1 f3 u d
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
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    (* failwith "Constprop.cp_block unimplemented" *)
    cfg
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
