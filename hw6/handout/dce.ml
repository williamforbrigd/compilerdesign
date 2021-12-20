(** Dead Code Elimination  *)
open Ll
open Datastructures


(* expose a top-level analysis operation ------------------------------------ *)
(* TASK: This function should optimize a block by removing dead instructions
   - lb: a function from uids to the live-OUT set at the 
     corresponding program point
   - ab: the alias map flowing IN to each program point in the block
   - b: the current ll block

   Note: 
     Call instructions are never considered to be dead (they might produce
     side effects)

     Store instructions are not dead if the pointer written to is live _or_
     the pointer written to may be aliased.

     Other instructions are dead if the value they compute is not live.

   Hint: Consider using List.filter
 *)
let dce_block (lb:uid -> Liveness.Fact.t) 
              (ab:uid -> Alias.fact)
              (b:Ll.block) : Ll.block =
  let new_insns = List.filter(fun insn -> 
    let u,i = insn in
    begin match i with
    | Call(ty, op, lst) -> true
    | Store(ty, op1, op2) -> 
      begin match op2 with
      | Id uid -> 
        let s = lb u in
        let m = ab u in
        (* print_endline (Liveness.Fact.to_string s);
        print_endline (Alias.Fact.to_string m); *)
        let is_live = UidS.mem uid s in
        let aliast = UidM.find_or Alias.SymPtr.UndefAlias m uid in
        begin match aliast with
        |Alias.SymPtr.MayAlias -> not is_live
        |_ -> is_live
        end
      |_ -> false
      end
    | _ ->
      let s = lb u in
      print_endline ("the uid is: " ^ u ^ " and the set: " ^ UidS.to_string s );
      UidS.mem u s
    end
    ) b.insns
  in
  {insns = new_insns; term = b.term}

let run (lg:Liveness.Graph.t) (ag:Alias.Graph.t) (cfg:Cfg.t) : Cfg.t =

  LblS.fold (fun l cfg ->
    let b = Cfg.block cfg l in

    (* compute liveness at each program point for the block *)
    let lb = Liveness.Graph.uid_out lg l in

    (* compute aliases at each program point for the block *)
    let ab = Alias.Graph.uid_in ag l in 

    (* compute optimized block *)
    let b' = dce_block lb ab b in
    Cfg.add_block l b' cfg
  ) (Cfg.nodes cfg) cfg

