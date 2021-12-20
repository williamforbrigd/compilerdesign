(** Alias Analysis *)

open Ll
open Datastructures

(* The lattice of abstract pointers ----------------------------------------- *)
module SymPtr =
  struct
    type t = MayAlias           (* uid names a pointer that may be aliased *)
           | Unique             (* uid is the unique name for a pointer *)
           | UndefAlias         (* uid is not in scope or not a pointer *)

    let compare : t -> t -> int = Pervasives.compare

    let join (t1 : t) (t2 : t) : t =
      match t1,t2 with
      |MayAlias, MayAlias -> MayAlias
      |Unique, Unique -> Unique
      |UndefAlias, UndefAlias -> UndefAlias
      
      |MayAlias, Unique -> Unique 
      |MayAlias, UndefAlias-> UndefAlias 

      |Unique, MayAlias-> Unique 
      |Unique, UndefAlias -> Unique 

      |UndefAlias, MayAlias -> UndefAlias 
      |UndefAlias,Unique-> Unique 
    
    let to_string = function
      | MayAlias -> "MayAlias"
      | Unique -> "Unique"
      | UndefAlias -> "UndefAlias"

  end

(* The analysis computes, at each program point, which UIDs in scope are a unique name
   for a stack slot and which may have aliases *)
type fact = SymPtr.t UidM.t

(* flow function across Ll instructions ------------------------------------- *)
(* TASK: complete the flow function for alias analysis. 

   - After an alloca, the defined UID is the unique name for a stack slot
   - A pointer returned by a load, call, bitcast, or GEP may be aliased
   - A pointer passed as an argument to a call, bitcast, GEP, or store
     may be aliased
   - Other instructions do not define pointers

 *)
let fact_to_string : fact -> string =
      UidM.to_string (fun _ v -> SymPtr.to_string v)

let f1 (a:'a) : 'a = SymPtr.Unique
let f2 (a:'a) : 'a = SymPtr.UndefAlias
let f3 (a:'a) : 'a = SymPtr.MayAlias

let ins_flow_union op u d = 
  begin match op with
  | Id uid ->
    let fact1 = UidM.update_or SymPtr.UndefAlias f3 uid d in
    let fact2 = UidM.update_or SymPtr.UndefAlias f3 u d in
    UidM.union (fun key a1 a2 -> Some(SymPtr.join a1 a1)) fact1 fact2
  |  _ -> UidM.update_or SymPtr.UndefAlias f3 u d
  end


let insn_flow ((u,i):uid * insn) (d:fact) : fact =
  match i with
  |Alloca ty -> UidM.update_or SymPtr.UndefAlias f1 u d
  |Bitcast(ty1, op, ty2) -> ins_flow_union op u d
  |Call(ty, op, lst) -> ins_flow_union op u d
  |Gep(ty, op, ops) -> ins_flow_union op u d

  (* |Load(ty, op) -> 
    begin match ty with
    |Ptr(ty1) -> 
      UidM.update_or SymPtr.MayAlias f3 u d
    |_ -> UidM.update_or SymPtr.MayAlias f3 u d
    end *)
  (*
  |Store(ty, op1, op2) -> 
    begin match op1 with
    |Id uid -> UidM.update_or SymPtr.MayAlias f3 uid d
    |_ -> UidM.update_or SymPtr.MayAlias f3 u d
    end *)

  | _ -> UidM.update_or SymPtr.UndefAlias f2 u d


(* The flow function across terminators is trivial: they never change alias info *)
let terminator_flow t (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    (* UndefAlias is logically the same as not having a mapping in the fact. To
       compare dataflow facts, we first remove all of these *)
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymPtr.UndefAlias)

    let compare (d:fact) (e:fact) : int = 
      UidM.compare SymPtr.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymPtr.to_string v)

    (* TASK: complete the "combine" operation for alias analysis.

       The alias analysis should take the join over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful.

       It may be useful to define a helper function that knows how to take the
       join of two SymPtr.t facts.
    *)

    let combine (ds:fact list) : fact =
      ds |> List.fold_left (fun acc elt -> 
        UidM.merge (fun k x0 y0 ->
          match x0, y0 with
          | Some x, Some y -> Some (SymPtr.join x y)
          | Some x, None -> Some x
          | None, Some y -> Some y
          ) acc elt 
        ) UidM.empty

  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefAlias *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any pointer parameter 
     to the function may be aliased *)
  let alias_in = 
    List.fold_right 
      (fun (u,t) -> match t with
                    | Ptr _ -> UidM.add u SymPtr.MayAlias
                    | _ -> fun m -> m) 
      g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init alias_in g in
  Solver.solve fg

