(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x ->  
(*let all = [Eq;Neq;Gt;Ge;Lt;Le] in *)
(if fo then
  if fs then
    if fz then (
      if x = Eq then true
      else if x = Le then true
      else if x = Ge then true
      else false
    )
    else (
      if x = Neq then true
      else if x = Gt then true
      else if x = Ge then true
      else false
    )
  else
    if fz then (
      if x = Eq then true
      else if x = Lt then true
      else if x = Le then true
      else false
    )
    else (
      if x = Neq then true
      else if x = Lt then true
      else if x = Le then true
      else false
    )
 (*not fo*)
else
  if fs then
    if fz then (
      if x = Eq then true
      else if x = Lt then true
      else if x = Le then true
      else false
    ) (*"fs + fz"*)
    else (
      if x = Neq then true
      else if x = Lt then true
      else if x = Le then true
      else false
    )
   (*not fs*)
  else if fz then (
    if x = Eq then true
    else if x = Ge then true
    else if x = Le then true
    else false
  )
  (*not fz*)
  else(
    if x = Neq then true
    else if x = Gt then true
    else if x = Ge then true
    else false
  ))

type 'a option = Some of 'a | None;;

let get_option_value (x: int option) : int =
    begin match x with
        |None->0
        |Some(value)->value
    end

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  begin match addr with
    |x->
        let y = 0xFFFFL in
        if (x >= mem_top || x < mem_bot) then None
        else
          Some (Int64.to_int (Int64.logand addr y))
  end

let string_of_sbyte (sb: sbyte) : string =
  let str : string = "" in
  begin match sb with
    |InsFrag->str ^ " InsFrag"
    |InsB0(ins)->str ^ " " ^ string_of_ins(ins)
    |Byte(b)->String.make 1 b
  end

let interpret_sbyte (sb:sbyte) : ins = 
  begin match sb with
    |InsB0(ins)->ins
  end

(*[Imm (Lit 8L); Reg Rsp]*)
(*Interpret operand that computes the source and destination information from the operands*)

let first_of_two (t: 'a * 'b) : 'a =
    begin match t with
        | (x, _) -> x
    end

let second_of_two (t: 'a * 'b) : 'b =
    begin match t with
        | (_, x) -> x
    end

let src_operand (lst: operand list) : operand =
    begin match lst with
        |(h::tl)->h
    end

let rec dest_operand (lst: operand list) : operand =
    begin match lst with
        |x::[]->x
        |(h::tl)->dest_operand tl
    end

let get_reg (op:operand) : reg =
    begin match op with
        |(Reg(x))->x
    end

let get_lit (op:operand) : int64 = begin match op with |Imm(Lit(x))->x end

let get_lit_value (imme:imm) : int64 = 
  begin match imme with 
    |Lit(x)->x 
    |Lbl(x)->
        Int64.of_string (String.sub x 1 ((String.length x)-1))
  end

let get_operation (oc:opcode) : string =
    begin match oc with
        |Addq->"+"
        |Subq->"-"
        |Imulq->"*"
        |_->raise Not_found
    end

let sbyte_list (a: sbyte array) (start: int) : sbyte list =
  Array.to_list (Array.sub a start 8)

let write_to_memory (value: int64) (src_index: int) (dest_arr:sbyte array) (dest_index: int) : unit = 
  Array.blit (Array.of_list (sbytes_of_int64 value)) src_index dest_arr dest_index (List.length (sbytes_of_int64 value));;

let get_reg_index (m:mach) (register:reg) : int = 
  let reg = m.regs.(rind register) in
  let mapped = map_addr reg in
  get_option_value mapped;;

let simulate_instruction_semantics (m:mach) (instr:ins) : unit =
    let opcode, operands = instr in
    let src = src_operand operands in
    let dest = dest_operand operands in
    begin match opcode with
        |Movq->
            begin match (src, dest) with
              |(Imm(x), Reg(y))->
                  m.regs.(rind y)<-get_lit_value x;
              |(Reg(x), Ind3(y1, y2))->
                  let dest_index = (get_reg_index m y2) + Int64.to_int (get_lit_value y1) in
                  write_to_memory (m.regs.(rind x)) 0 m.mem dest_index; 
              |(Imm(x), Ind3(im, r)) ->
                let idx = (get_reg_index m r) in
                Array.blit (Array.of_list (sbytes_of_int64 (get_lit_value x))) 0 m.mem idx (List.length (sbytes_of_int64 (get_lit_value x)));
            end
        |Andq->
          begin match (src, dest) with
            |Reg(x), Reg(y) ->
                let reg1 = m.regs.(rind x) in
                let reg2 = m.regs.(rind y) in
                let calc = Int64.logand reg2 reg1 in
                m.regs.(rind y) <- calc;
            |Imm(x), Reg(y) ->
                let val1 = (get_lit_value x) in
                let reg2 = m.regs.(rind y) in
                let calc = Int64.logand reg2 val1 in
                m.regs.(rind y) <- calc;
            |Ind3(x1, x2), Reg(y) ->
                let val1 = (int64_of_sbytes ((Array.get m.mem (get_reg_index m x2))::[])) in
                let reg2 = m.regs.(rind y) in
                let calc = Int64.logand reg2 val1 in
                m.regs.(rind y) <- calc;
          end
        |Negq->
            begin match dest with
              |Reg(r)->
                  let reg_value = m.regs.(rind r) in
                  if reg_value == Int64.min_int then m.flags.fo <- true
                  else m.regs.(rind r) <- Int64.neg (reg_value);
                  let val2 = (int64_of_sbytes ((Array.get m.mem (get_reg_index m Rsp))::[])) in
                   m.flags.fs <- ((Int64.shift_right_logical (Int64.neg (reg_value)) 63) = 1L); m.flags.fz <- ((Int64.neg (reg_value)) = (Int64.zero));
              |Ind3(im, r)->
                  let val1 = (int64_of_sbytes ((Array.get m.mem (get_reg_index m r))::[])) in
                  let idx = (get_reg_index m Rsp) in
                  if val1 == Int64.min_int then (
                    m.flags.fo <- true;
                    write_to_memory val1 0 m.mem idx;
                    m.flags.fs <- true; m.flags.fz <- false;
                    )
                  else (
                    write_to_memory (Int64.neg val1) 0 m.mem idx;
                    m.flags.fs <- ((Int64.shift_right_logical ((Int64.neg val1)) 63) = 1L); m.flags.fz <- ((Int64.neg val1) = (Int64.zero));
                  )
            end
        |Addq->
            begin match (src,dest) with
              |(Imm(x), Reg(y))->
                let calc =Int64_overflow.add (m.regs.(rind y)) (get_lit_value x) in
                m.regs.(rind y) <- calc.value;
                m.flags.fo <- calc.overflow; m.flags.fs <- ((Int64.shift_right_logical calc.value 63) = 1L); m.flags.fz <- ((calc.value) = (Int64.zero));
              |(Reg(x), Reg(y))->
                  let reg1 = m.regs.(rind x) in
                  let reg2 = m.regs.(rind y) in
                  let calc = Int64_overflow.add reg2 reg1 in
                  m.regs.(rind y) <- calc.value;
                  m.flags.fo <- calc.overflow; m.flags.fs <- ((Int64.shift_right_logical calc.value 63) = 1L); m.flags.fz <- ((calc.value) = (Int64.zero));
              |(Reg(x), Ind3(im, r))->
                  let reg1 = m.regs.(rind x) in
                  let val2 = (int64_of_sbytes ((Array.get m.mem (get_reg_index m r))::[])) in
                  let calc = Int64_overflow.add (get_lit_value im) reg1 in
                  let idx = (get_reg_index m Rsp) in
                  Array.blit (Array.of_list (sbytes_of_int64 (calc.value))) 0 m.mem idx (List.length (sbytes_of_int64 (calc.value)));
                    m.flags.fo <- calc.overflow; m.flags.fs <- ((Int64.shift_right_logical calc.value 63) = 1L); m.flags.fz <- ((calc.value) = (Int64.zero));
            end
        |Subq ->
          begin match (src, dest) with
            |(Imm(x), Reg(y))->
              let calc =Int64_overflow.sub (m.regs.(rind y)) (get_lit_value x) in
              m.regs.(rind y) <- calc.value;
              m.flags.fo <- calc.overflow; m.flags.fs <- ((Int64.shift_right_logical calc.value 63) = 1L); m.flags.fz <- ((calc.value) = (Int64.zero));
            |(Reg(x), Reg(y))->
                let reg1 = m.regs.(rind x) in
                let reg2 = m.regs.(rind y) in
                let calc = Int64_overflow.sub reg2 reg1 in
                m.regs.(rind y) <- calc.value;
                m.flags.fo <- calc.overflow; m.flags.fs <- ((Int64.shift_right_logical calc.value 63) = 1L); m.flags.fz <- ((calc.value) = (Int64.zero));
            |(Reg(x), Imm(y))->
              m.regs.(rind x)<- get_lit_value y;
            |(Reg(x), Ind3(y)) ->
              let (im, r) = y in
              let reg1 = m.regs.(rind x) in
              let val2 = (int64_of_sbytes ((Array.get m.mem (get_reg_index m r))::[])) in
              let calc = Int64_overflow.sub (get_lit_value im) reg1 in
              let idx = (get_reg_index m Rsp) in
              Array.blit (Array.of_list (sbytes_of_int64 (calc.value))) 0 m.mem idx (List.length (sbytes_of_int64 (calc.value)));
                m.flags.fo <- calc.overflow; m.flags.fs <- ((Int64.shift_right_logical calc.value 63) = 1L); m.flags.fz <- ((calc.value) = (Int64.zero));
          end
        |Imulq->
            begin match (src, dest) with
              |(Reg(x), Reg(y))->
                let reg1 = m.regs.(rind x) in
                let reg2 = m.regs.(rind y) in
                let calc = Int64_overflow.mul reg1 reg2 in
                m.regs.(rind y) <- calc.value;
                m.flags.fo <- calc.overflow; m.flags.fs <- ((Int64.shift_right_logical calc.value 63) = 1L); m.flags.fz <- ((calc.value) = (Int64.zero));
            end
        |Shlq->
          begin match (src, dest) with
            | (Imm(x), Reg(y)) ->
              let val1 = get_lit_value x in
              let reg2 = m.regs.(rind y) in
              let calc = Int64.shift_left reg2 (Int64.to_int val1) in
              m.regs.(rind y) <- calc;
            | (Reg(x), Ind3(y)) ->
              let (im, r) = y in
              let reg1 = m.regs.(rind x) in
              let val2 = (int64_of_sbytes ((Array.get m.mem (get_reg_index m r))::[])) in
              let calc = Int64.shift_left val2 (Int64.to_int reg1) in
              let idx = (get_reg_index m r) in
              Array.blit (Array.of_list (sbytes_of_int64 (calc))) 0 m.mem idx (List.length (sbytes_of_int64 (calc)));
              m.regs.(rind r) <- Int64.of_int idx;
          end
        |Pushq ->
          begin match (dest) with
            | Imm(x) ->
              m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) (Int64.of_int (List.length (sbytes_of_int64 (get_lit_value x))));
              let idx = (get_reg_index m Rsp) in
              Array.blit (Array.of_list (sbytes_of_int64 (get_lit_value x))) 0 m.mem idx (List.length (sbytes_of_int64 (get_lit_value x)));
          end
        |Popq->
          begin match dest with
            |Reg(r)->
                let mem_rsp = get_reg_index m Rsp in
                m.regs.(rind r) <- Int64.of_int mem_rsp;
                m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L;
          end
        | _ -> ()
    end


(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit =
  (*fetch information at rip*)
  let rip = m.regs.(rind Rip) in
  m.regs.(rind Rip) <- Int64.add (m.regs.(rind Rip)) ins_size;
  let ins_index = map_addr rip in
  let sbyte = m.mem.(get_option_value ins_index) in
  let ins = interpret_sbyte sbyte in
  let opcode = first_of_two ins in
  let operands = second_of_two ins in
  let src = src_operand operands in
  let dest = dest_operand operands in
  (*simulate instruction semantics*)
  simulate_instruction_semantics m ins;;

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* startinng address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let get_char_array s : sbyte list =
  let rec exp i l : sbyte list =
    if i < 0 then l else exp (i - 1) ((Byte s.[i])::l) in
  exp (String.length s - 1) []

let get_char_array s : sbyte list =
  let rec exp i l : sbyte list =
    if i < 0 then l @ [Byte (Char.chr 0)] else exp (i - 1) ((Byte s.[i])::l) in
  exp (String.length s - 1) []

let get_byte_array (i:int64) : sbyte list =
  [Byte (Char.chr (Int64.to_int (Int64.logand 0x00000000000000FFL i)));
  Byte (Char.chr (Int64.to_int (Int64.logand 0x000000000000FF00L i)));
  Byte (Char.chr (Int64.to_int (Int64.logand 0x0000000000FF0000L i)));
  Byte (Char.chr (Int64.to_int (Int64.logand 0x00000000FF000000L i)));
  Byte (Char.chr (Int64.to_int (Int64.logand 0x000000FF00000000L i)));
  Byte (Char.chr (Int64.to_int (Int64.logand 0x0000FF0000000000L i)));
  Byte (Char.chr (Int64.to_int (Int64.logand 0x00FF000000000000L i)));
  Byte (Char.chr (Int64.to_int (Int64.logand 0xFF00000000000000L i)))]

let rec get_data_seg (d:data list) : sbyte list =
  begin match d with
  | hd::tl -> begin match hd with
    | Asciz x -> (get_char_array x) @ (get_data_seg tl)
    | Quad y -> begin match y with
      | Lit yy -> (get_byte_array yy) @ (get_data_seg tl)
      | _ -> raise (Undefined_sym "test")
      end
    end
  | [] -> []
  end

let rec find_main (p:prog) =
begin match p with
 | hd::tl -> if (hd.lbl = "main") then ()
 else
    (
     begin match hd.asm with
       | X86.Data x -> find_main tl
       | X86.Text t -> find_main tl
       end
       )
 | [] -> raise  (Undefined_sym "main")
 end

let rec find_label (label:string) (p:prog) (sum: int64) : int64 =
begin match p with
 | hd::tl -> if (hd.lbl = label) then (Int64.add 1L sum)
 else
    (
     begin match hd.asm with
       | X86.Data x ->  find_label label tl (Int64.add sum (Int64.of_int(List
       .length x)))
       | X86.Text t ->find_label label tl (Int64.add sum (Int64.of_int(List.length t)))
       end
       )
 | [] -> (raise  (Undefined_sym label))
 end

 let replace_label (p: prog) (sum: int64) (op:operand): operand =
  begin match op with
  | Ind1 x -> begin match x with
              |  Lbl xx ->
                Ind1 (Lit (Int64.add 0x400000L (Int64.mul (find_label xx p sum) 8L)))
              | y -> op
             end
  | Imm x -> begin match x with
              | Lbl xx ->
                  Imm (Lit (Int64.add 0x400000L (Int64.mul (find_label xx p sum) 8L)))
              | y -> op
              end
  | Ind3 (x1, x2) -> begin match x1 with
              | Lbl y -> Ind3 ((Lit (Int64.add 0x400000L (Int64.mul (find_label y p sum) 8L))), x2)
              | yy -> op
              end
  | _ -> op
  end
 let rec get_text_seg (input:ins list) (sum: int64) (p:prog) : sbyte list =
 begin match input with
  | hd::tl -> let (r1, r2) = hd in
      InsB0 (r1, (List.map (replace_label p sum) r2))
      ::InsFrag::InsFrag::InsFrag::InsFrag::InsFrag::InsFrag::InsFrag::
      (get_text_seg tl (Int64.add sum (Int64.of_int(List.length r2))) p)
  | [] -> []
end
 let rec assmbl (p:prog) (e:exec) : exec =
 begin match p with
   | hd::tl ->
       begin match hd.asm with
         | X86.Data x ->
           assmbl tl { entry = e.entry; text_pos = e.text_pos; data_pos = Int64.add mem_bot (Int64.of_int(List.length e.text_seg)); text_seg = e.text_seg;
           data_seg = e.data_seg @ (get_data_seg x)}
         | X86.Text t ->
            assmbl tl { entry = e.entry; text_pos = e.text_pos; data_pos = Int64.add mem_bot (Int64.of_int(List.length e.text_seg)); text_seg =
            e.text_seg @ (get_text_seg t 0L p); data_seg = e.data_seg}
         end
   | [] -> e
 end

let assemble (p:prog) : exec =
let test = { entry = 0x400000L; text_pos = 0x400000L; data_pos = 0x400000L; text_seg = [];data_seg = []} in
  find_main p;
  assmbl p test



(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let adp (entry:quad) (i:int64) : int64 =
  (Int64.add i entry)

let load {entry; text_pos; data_pos; text_seg; data_seg} : mach =
(*todo vet ikke om rsp er satt riktig, heller ikke av noen av de andre registrene lmao*)
let lt = [0L;1L;2L;3L;4L;5L;6L;0xfff0L;8L;9L;10L;11L;12L;13L;14L;15L;0L] in
let mem = Array.make mem_size (Byte '\000') in
let exit_bytes = Array.of_list (sbytes_of_int64 exit_addr) in
(*copy exit code to last part of array*)
Array.blit exit_bytes 0 mem 0x0fff8 8;
(*copy both text and data to memory*)
let instruction_bytes = Array.of_list(text_seg @ data_seg) in
Array.blit instruction_bytes 0 mem (0) (Array.length instruction_bytes);
let ex = { entry = entry; text_pos = text_pos; data_pos = data_pos; text_seg = text_seg;data_seg = data_seg} in
let test = {flags = {fo = false; fs = false; fz = false}; regs = (Array.of_list (List.map (adp entry) lt));
mem = mem} in test
