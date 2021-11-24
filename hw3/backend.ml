(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

let first_of_two (t: 'a * 'b) : 'a =
  begin match t with
    |(x,_)->x
  end

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

let rec print_layout (l:layout) =
 begin match l with
 | hd::tl ->
  begin match hd with
    | (a, b) ->
             print_endline ("uid is: " ^ a);
             print_endline ("operand is: " ^ string_of_operand(b));
             print_layout tl;
  end
  |hd::[] ->
  begin match hd with
    | (a, b) ->
             print_endline ("uid is: " ^ a);
             print_endline ("operand is: " ^ string_of_operand(b));
  end
 | _ -> print_endline "printing layout done";
 end
(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
    fun op -> 
      begin match op with
        (*TODO handle if the operand is Null*)
        |Const(v)->
            (Movq, [Imm(Lit(v)); dest])
        |Id(uid)-> 
          let src = lookup ctxt.layout uid in
          (Movq, [src; dest])
        |Gid(gid)->
            let glabel = Platform.mangle gid in
            (*Rule number 2*)
            begin match dest with
              |Imm(imm)->
                (*Compute the %rip-relative address using the leaq*)
                  (Leaq, [Ind3(Lbl(glabel), Rip)])
            end
      end



(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)

(*let rec compile_call(t:Ll.ty) (op1:operand) (param_types: (ty * operand) list) : ins list = *)


let first_of_two (t: 'a * 'b) : 'a = 
  begin match t with
    |(x,_)->x
  end

let second_of_two (t: 'a * 'b) : 'b = 
  begin match t with
    |(_, x)->x
  end

let arg_loc (n : int) : operand =
begin match n with
  | 0 -> X86.Reg Rdi
  | 1 -> X86.Reg Rsi
  | 2 -> X86.Reg Rdx
  | 3 -> X86.Reg Rcx
  | 4 -> X86.Reg R08
  | 5 -> X86.Reg R09
  (*First six are passed in registers, rest are passed on stack*)
  (*todo er n - 4 riktig her? ?? ? ? ? ??*)
  | _ -> Ind3 (Lit (Int64.mul 8L (Int64.of_int(n - 4))), Rbp)
end


(*TODO need a way of cleaning the stack before the return*)
(*
let clean_stack (n : int) : ins list = 
  if n <> 0 
    then (Addq, [Imm(Lit(Int64.mul (Int64.of_int n) 8L)); Reg Rsp])::[]
  else [];;
*)

let compile_call (ty:Ll.ty) (op:Ll.operand) (param_types: (Ll.ty * Ll.operand) list) ctxt uid : ins list = 
  print_endline ("the uid is: " ^ uid);
  print_endline (X86.string_of_operand (lookup ctxt.layout uid));
  print_endline ("The type is: " ^ Llutil.string_of_ty ty);
  print_endline ("The operand is: " ^Llutil.string_of_operand op);
  param_types
  |> List.fold_left (fun init el -> init ^ "Type: " ^ Llutil.string_of_ty (first_of_two el)^ " Operand: " ^ Llutil.string_of_operand (second_of_two el)) "" 
  |> print_endline;
  begin match op with
    (*Global function type*)
    |Gid(gid)->
        print_endline ("The gid is: " ^gid);
        let counter = ref 0 in 
        let rec compile_param_types param_types counter acc = 
          begin match param_types with
            |[]->
                acc @ [(Callq, [Imm(Lbl(gid));]); (Movq, [Reg Rax; lookup ctxt.layout uid])]
            |(h::tl)->
                begin match h with
                  |(ty1, op1)->
                    let reg = arg_loc !counter in
                    counter := !counter + 1;
                    begin match op1 with
                      |Null->acc
                      |Const(v)-> compile_param_types tl counter ((Movq, [Imm(Lit(v)); reg])::acc)
                      |Id(uid)->compile_param_types tl counter ((Movq, [lookup ctxt.layout uid; reg])::acc)
                      (*
                      |Gid(gid1)->
                        let glabel = Platform.mangle gid in
                        (*Should it be Imm, Ind1 or Ind3???*)
                        (Movq, [Imm(Lbl(glabel)); reg])::acc
                        *)
                    end
                end
          end
        in compile_param_types param_types counter [] 
  end

(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)

let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
  begin match t with
  | Array (x, y) -> x * (size_ty tdecls y)
  | Struct x -> List.fold_left (fun add y -> add + size_ty tdecls y) 0 x
  | Namedt x -> size_ty tdecls (List.assoc x tdecls)
  (*todo er dette riktig ? bryr jeg meg, testene går jo :)*)
  | _ -> 8
  end


(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
  (*TODO all operands must be constants, unless they are used to index an array*)
  (*Use 64 bit integers for indexing*)
  print_endline "\ntrying to compile gep";
  print_endline (Llutil.string_of_ty (first_of_two op));
  print_endline (Llutil.string_of_operand (second_of_two op));
  path 
  |>List.fold_left (fun init el-> init ^ Llutil.string_of_operand el) "The path is: \n"
  |>print_endline;
  (*
  let rec GEPTY op path acc = 
    begin match path with
      |T::[]->T

    end
    *)
  [];;




(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)

let src_operand (ins: X86.ins) : X86.operand = 
  begin match ins with
    |(_, operands)->
        begin match operands with
          |h::tl->h
        end
  end

let dest_operand(ins: X86.ins) : X86.operand = 
  begin match ins with
    |(_, operands)->
        let rec dest_operand_acc operands =
          begin match operands with
            |[h]->h
            |h::tl->dest_operand_acc tl
          end
        in dest_operand_acc operands
  end

let math_op (a:bop) (b:ty) (op1:Ll.operand) (op2:Ll.operand) (operation:opcode) (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  let f1 = compile_operand ctxt (lookup ctxt.layout uid) in
          let ins1 = f1 op1 in
          begin match op2 with
            |Const(v)->
              if (operation = Imulq)
              then
              (
                print_endline ("ins1 is " ^ (string_of_ins ins1));
                let insns =
                [
                ins1;
                (*todo har det noe å si hvilket register vi bruker ? R08 er general purpose så*)
                (Movq, [(lookup ctxt.layout uid); Reg R08]);
                (operation, [Imm(Lit(v)); Reg R08]);
                (Movq, [Reg R08; (lookup ctxt.layout uid)])
                ] in
                insns
              ) else
              (
              print_endline ("ins1 is " ^ (string_of_ins ins1));
              let insns =
              [ins1; (operation, [Imm(Lit(v)); (lookup ctxt.layout uid)])] in
              List.fold_left (fun init el -> init ^ "\n" ^ (X86.string_of_ins el)) "" insns |> print_endline;
              insns
              )
          end

let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  begin match i with
    |Binop(bop, ty, op1, op2)->
      print_endline ("Uid: " ^ uid);
      print_endline (X86.string_of_operand (lookup ctxt.layout uid));
      print_endline (Llutil.string_of_bop bop);
      print_endline (Llutil.string_of_ty ty);
      print_endline (Llutil.string_of_operand op1);
      print_endline (Llutil.string_of_operand op2);
      begin match bop with
        |Add->
          math_op bop ty op1 op2 Addq ctxt (uid, i)
        |Sub->
          math_op bop ty op1 op2 Subq ctxt (uid, i)
        |And->
          math_op bop ty op1 op2 Andq ctxt (uid, i)
        |Xor->
          math_op bop ty op1 op2 Xorq ctxt (uid, i)
        |Or->
          math_op bop ty op1 op2 Orq ctxt (uid, i)
        |Mul->
          math_op bop ty op1 op2 Imulq ctxt (uid, i)
        |Shl ->
          math_op bop ty op1 op2 Shlq ctxt (uid, i)
        |Lshr ->
          math_op bop ty op1 op2 Shrq ctxt (uid, i)
        |Ashr ->
          math_op bop ty op1 op2 Sarq ctxt (uid, i)
      end
    |Icmp(cnd, ty, op1, op2)->
      let f1 = compile_operand ctxt (lookup ctxt.layout uid) in
      let ins1 = f1 op1 in
      print_endline("halla hva skjer"^X86.string_of_ins ins1);
      begin match op2 with
        |Const(v)->
            [ins1; (Cmpq, [Imm(Lit(v)); lookup ctxt.layout uid])]
        |Id(uid2)->
            [ins1; (Cmpq, [lookup ctxt.layout uid2; lookup ctxt.layout uid])]
        (*TODO does the global operand have to be compiled??*)
        (*
        |Gid(gid)->
            *)
            (*let ins2 = compile_operand ctxt (lookup ctct.layout gid) in*)
      end
    |Alloca(ty)->
        let size = size_ty ctxt.tdecls ty in
        print_endline ("The size is: " ^string_of_int size);
        [Subq, [Imm(Lit(Int64.of_int size)); Reg Rsp]]
    |Load(ty, op)->
        print_endline (Llutil.string_of_ty ty);
        print_endline (Llutil.string_of_operand op);
        begin match op with
          |Id(uid1)->
            begin match ty with
              |Ptr(ty1)->
                begin match ty1 with
                  |I64->
                    (*Alle eksemplene har Rax, skal noe annet reg brukes?*)
                    [
                      Movq, [Imm(Lit(17L)); Ind3(Lit(-16L) , Rsp)];
                      (*todo flytter -16 fordi _store_ 1 tar opp 8, og hvis uid funker bare for *)
                      Subq, [Imm(Lit(-16L)); Reg Rsp]
                    ]
                  (*TODO double pointer*)
                  |Ptr(ty2)->
                    begin match ty2 with
                      |I64->
                      []
                    end
                end
          |_->failwith("type must be pointer or undefined")
        end
        end
    |Store(ty, op1, op2)->
        begin match ty with
          |I64->
            begin match (op1, op2) with
              |(Const(v), Id(uid1))->
                      print_endline "it's this one ------------------------";
                print_layout ctxt.layout;
                print_endline ("second layout is " ^ uid1);
                [Movq, [Imm(Lit(v)); lookup ctxt.layout uid1]]
              |(Id(uid1), Id(uid2))->
                  [Movq, [lookup ctxt.layout uid1; lookup ctxt.layout uid2]]
            end
          |Ptr(ty1)->
              begin match ty1 with
                |I64->
                  begin match (op1, op2) with
                    |(Const(v), Id(uid1))->
                      [Movq, [Imm(Lit(v)); lookup ctxt.layout uid1]]
                    |(Id(uid1), Id(uid2))->
                      print_endline "it's that one";
                      [Movq, [lookup ctxt.layout uid1; lookup ctxt.layout uid2]]
                  end
              end
        end
    |Call(ty, op1, lst)->
        compile_call ty op1 lst ctxt uid
    |Bitcast(ty1, op, ty2)->
        print_endline (Llutil.string_of_ty ty1);
        print_endline (Llutil.string_of_operand op);
        print_endline (Llutil.string_of_ty ty2);
        (*TODO trenger vi implementere noe her siden X86 er untyped?*)
        []
    |Gep(ty, op, path)->
        compile_gep ctxt (ty, op) path
    | _ ->
      print_endline "something else -----------------------";
      failwith "not impl"
  end



(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are 
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let second_of_two (t: 'a * 'b) : 'b =
  begin match t with
    |(_, x)->x
  end

let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  let insns : ins list = [] in
  begin match t with
    |Ret(ty, op)->
        begin match ty with
          (*todo alle kan vel se like ut, eller skal man tømme RAX hvis det er void?*)
          |Void->(Retq, [])::insns
          (*todo: bare placeholder for at denne skal passe på return.ll, kan slettes*)
          |I64->
            begin match op with
              | None -> (Retq, [])::insns
              | Some x ->
                begin match x with
                  | Const y ->
                    print_endline "const ---------------";
                    [
                      Movq, [X86.Asm.(~$ (Int64.to_int y) ); X86.Asm.(~%Rax)];
                      Movq, [X86.Asm.(~%Rbp); X86.Asm.(~%Rsp)];
                      Popq, [X86.Asm.(~%Rbp)];
                      Retq, []
                    ] @ insns
                  (*todo what does it mean to return a global identifier string ?*)
                  | Gid y ->
                    print_endline "gid ----------------";
                    [
                      Popq, [X86.Asm.(~%Rbp)];
                      Retq, []
                    ] @ insns
                  (*todo what does it mean to return a local identifier string*)
                  | Id y ->
                    print_endline ("id -----------" ^ y);
                    [
                      Movq, [(lookup ctxt.layout y); Reg Rax];
                      Movq, [X86.Asm.(~%Rbp); X86.Asm.(~%Rsp)];
                      Popq, [X86.Asm.(~%Rbp)];
                      Retq, []
                    ] @ insns
                  | _ ->
                    print_endline "other ---------------";
                    [
                      Popq, [X86.Asm.(~%Rbp)];
                      Retq, []
                    ] @ insns
                end
            end
        end
    |Br(label) ->
      print_endline ("function is: " ^ fn);
      [
        Movq, [Imm(Lit(9L)); X86.Asm.(~%Rax)];
        Movq, [X86.Asm.(~%Rbp); X86.Asm.(~%Rsp)];
        Popq, [X86.Asm.(~%Rbp)];
        Retq, []
        (*Jmp, [X86.Asm.(~$$label)]*)
      ] @ insns
    |Cbr(x, y, z) ->
      begin match x with
       | Const(x) ->
          print_endline "jeg hater const";
          print_endline (Int64.to_string x);
       | Gid(x) ->
       print_endline x;
       | Id(x) ->
       print_endline x;
      end;
      [
        Movq, [Imm(Lit(9L)); X86.Asm.(~%Rax)];
        Movq, [X86.Asm.(~%Rbp); X86.Asm.(~%Rsp)];
        Popq, [X86.Asm.(~%Rbp)];
        Retq, []
        (*Jmp, [X86.Asm.(~$$label)]*)
      ] @ insns
  end

(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. 
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let rec compile_insn_list (ctxt:ctxt) (tempo: (uid * Ll.insn) list) : X86.ins list =
begin match tempo with
 | hd::tl -> (compile_insn ctxt hd) @ (compile_insn_list ctxt tl)
 | [] -> []
end

let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  begin match blk.insns with
    (*TODO the term has a uid as well*)
    |[]->compile_terminator fn ctxt (second_of_two blk.term);
    | hd::tl ->
      (compile_insn_list ctxt blk.insns) @ (compile_terminator fn ctxt (second_of_two blk.term))
  end


let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
begin match n with
  | 0 -> X86.Reg Rdi
  | 1 -> X86.Reg Rsi
  | 2 -> X86.Reg Rdx
  | 3 -> X86.Reg Rcx
  | 4 -> X86.Reg R08
  | 5 -> X86.Reg R09
  (*First six are passed in registers, rest are passed on stack*)
  (*todo er n - 4 riktig her? ?? ? ? ? ??*)
  | _ -> Ind3 (Lit (Int64.mul 8L (Int64.of_int(n - 4))), Rbp)
  end

let compute_offset (n:int) : operand = 
  begin match n with
    | 0 -> Ind2(Rbp)
    | _ -> Ind3 (Lit (Int64.mul 8L (Int64.neg(Int64.of_int n))), Rbp)
  end

let layout_from_block (insns: (uid * insn) list) (counter: int) : layout =
  let rec layout_from_block_acc acc insns counter = 
    begin match insns with
      |[]->acc
      |h::tl->
        let uid = first_of_two h in
        let operand = compute_offset counter in
        layout_from_block_acc ((uid, operand)::acc) tl (counter+1)
    end
  in layout_from_block_acc [] insns counter;;

let layout_from_blocks (blocks: (lbl * block) list) (counter: int) : layout =
  let rec layout_from_blocks_acc acc blocks counter = 
    begin match blocks with
      |[]->acc
      |h::tl->
          let block = second_of_two h in
          let layout_block = layout_from_block block.insns counter in
          layout_from_blocks_acc (layout_block @ acc) tl (counter+1)
    end
  in layout_from_blocks_acc [] blocks counter;;

let layout_from_args (args : uid list) (counter : int) : layout = 
  let rec layout_from_args_acc args counter acc = 
    begin match args with
      |[]->acc
      |h::tl->
          let operand = compute_offset counter in
          layout_from_args_acc tl (counter+1) ((h, operand)::acc)
    end
  in layout_from_args_acc args counter []



let layout_from_block (insns: (uid * insn) list) (counter: int ref) : layout =
  let rec layout_from_block_acc acc insns counter =
    begin match insns with
      |[]->acc
      |h::tl->
        let uid = first_of_two h in
        let operand = arg_loc !counter in
        counter := !counter + 1;
        layout_from_block_acc ((uid, operand)::acc) tl counter
    end
  in layout_from_block_acc [] insns counter;;

let layout_from_blocks (blocks: (lbl * block) list) (counter: int ref) : layout =
  let rec layout_from_blocks_acc acc blocks counter =
    begin match blocks with
      |[]->acc
      |h::tl->
          let block = second_of_two h in
          let layout_block = layout_from_block block.insns counter in
          layout_from_blocks_acc (layout_block @ acc) tl counter
    end
  in layout_from_blocks_acc [] blocks counter;;

(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
let stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout =
  (*First move the args into the stack layout*)
  (*Counter starts at 1 because %1 is the name of the first basic block*)
  args |> List.fold_left (fun init el-> init ^el) "The args is: " |> print_endline;
  let counter : int  = 1 in
  let lst = [] in
  let args_layout = layout_from_args args counter in
  let counter = ref 1 in
  let b1_layout = layout_from_block block.insns counter in
  let blocks_layout = layout_from_blocks lbled_blocks counter in
  args_layout @ b1_layout @ blocks_layout;;

  
(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)

let print_el init el : string = 
  init ^ Llutil.string_of_ty el ^ " ";;


let rec compile_labeled_blocks (fn:string) (ct : ctxt) (blocks :(Ll.lbl * Ll.block) list) : elem list=
  begin match blocks with
          (*
            let compile_lbl_block fn lbl ctxt blk : elem =
          *)
    | hd::tl ->
      ((compile_lbl_block fn (first_of_two hd) ct (second_of_two hd))::(compile_labeled_blocks fn ct tl));
    | hd::[] ->
      ((compile_lbl_block fn (first_of_two hd) ct (second_of_two hd))::[]);
    | _ -> [];
  end


let cfg_blocks (tdecls: (tid * ty) list) (name:string) ({f_ty; f_param; f_cfg}:fdecl) : elem list =
  begin match f_cfg with
    |(block, lbled_blocks)->
        (*The args are the function arguments*)
        let layout = stack_layout f_param (block, lbled_blocks) in
        let ctxt = {tdecls = tdecls; layout = layout; } in
        (*TODO compile all the instructions in the block*)
        compile_labeled_blocks name ctxt lbled_blocks;
  end


let compile_cfg (tdecls: (tid * ty) list) (name:string) ({f_ty; f_param; f_cfg}:fdecl) : ins list = 
  begin match f_cfg with
    |(block, lbled_blocks)->
        (*The args are the function arguments*)
        let layout = stack_layout f_param (block, lbled_blocks) in
        let ctxt = {tdecls = tdecls; layout = layout; } in
        compile_block name ctxt block;
  end


let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_ty; f_param; f_cfg }:fdecl) : prog =
  tdecls |> List.fold_left (fun init el -> init ^ "Tid: " ^ (first_of_two el) ^ Llutil.string_of_ty (second_of_two el)) "The type declarations are: \n" |> print_endline;

  print_endline ("name of program: " ^ name);
  print_endline (Printf.sprintf "length of program: %d" (List.length tdecls));
  begin match f_ty with
    | (a, b) -> 
        print_endline ("return type is: " ^ (Llutil.string_of_ty b));
        a |> List.fold_left print_el "" |> print_endline;
  end;
  f_param |> List.fold_left (fun init el -> init ^ " " ^ el) "param: " |> print_endline;
  let (a, b) = f_cfg in
  print_endline (string_of_int (List.length b));

  let cfg_insns = compile_cfg tdecls name {f_ty; f_param; f_cfg} in
  let cfg_lbld_blocks = cfg_blocks tdecls name {f_ty; f_param; f_cfg} in
  cfg_lbld_blocks
  |>List.fold_left (fun init el-> init ^ X86.string_of_elem el) "The labeled blocks is: \n"
  |>print_endline;

  let insns =
    [
    (Pushq, [Reg(Rbp)]);
      (Movq, [Reg(Rsp); Reg(Rbp)]);
      ] in
  let elem = Asm.gtext name (insns @  cfg_insns) in
  let program : prog = [elem] @ cfg_lbld_blocks in
  program

(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
