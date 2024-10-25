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
    | _ -> ()
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


(* override some useful operators  *)
let ( +. ) = Int64.add
let ( -. ) = Int64.sub
let ( *. ) = Int64.mul
let ( <. ) a b = (Int64.compare a b) < 0
let ( >. ) a b = (Int64.compare a b) > 0
let ( <=. ) a b = (Int64.compare a b) <= 0
let ( >=. ) a b = (Int64.compare a b) >= 0
let ( ?> ) = Int64.to_int
let ( ?< ) = Int64.of_int

(* Interpret a condition code with respect to the given flags. *)
(* !!! Check the Specification for Help *)
let interp_cnd {fo; fs; fz} : cnd -> bool = function
  | Eq -> fz
  | Neq -> not fz
  | Lt -> fs <> fo
  | Ge -> fs = fo
  | Le -> (fs <> fo) || fz
  | Gt -> (fs = fo) && not fz


(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if addr >=. mem_bot && addr < mem_top then
    Some ?>(addr -. mem_bot)
  else
    None

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* Maps an X86lite address into Some OCaml array index,
 * or raise X86lite_segfault when addr is not within the
 * legal address space. *)
let map_addr_segfault (addr:quad) : int =
  match map_addr addr with
  | None -> raise X86lite_segfault
  | Some index -> index
let map_addr_safe = map_addr_segfault

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags

  We provide the basic structure of step function and helper functions.
  Implement the subroutine below to complete the step function.
  See step function to understand each subroutine and how they 
  are glued together.
*)

exception Invalid_ins
let fetchins (m:mach) (addr:quad) : ins =
  let index = map_addr_safe addr in
  match m.mem.(index) with
    | InsB0 insn -> insn
    | _ -> raise Invalid_ins
let fetch_ins = fetchins

let readquad (m:mach) (addr:quad) : quad =
  let index = map_addr_safe addr in
  int64_of_sbytes Array.(sub m.mem index 8 |> to_list)
let read_quad = readquad

let writequad (m:mach) (addr:quad) (w:quad) : unit =
  let index = map_addr_safe addr in
  Array.blit (Array.of_list @@ sbytes_of_int64 @@ w) 0 m.mem index 8
let write_quad = writequad

let rget (m: mach) (r: reg) : int64 = m.regs.(rind r)
let rset (m: mach) (r: reg) (i: int64) : unit = m.regs.(rind r) <- i

exception Invalid_ind_oprnd
let interp_ind (m: mach) : operand -> quad =
  let rget = rget m in
  function
  | Ind1 Lit i -> i
  | Ind2 r -> rget r
  | Ind3 (Lit i, r) -> rget r +. i
  | _ -> raise Invalid_ind_oprnd

exception Invalid_val_oprnd
let interp_val (m: mach) (oprnd: operand) : int64 =
  match oprnd with
  | Imm Lit i -> i
  | Reg r -> rget m r
  | Ind1 _ | Ind2 _ | Ind3 _ -> read_quad m (interp_ind m oprnd)
  | _ -> raise Invalid_val_oprnd

exception Invalid_dest
let set_dest_val (m: mach) (dst: operand) (value: int64) : unit =
  match dst with
  | Reg r -> rset m r value
  | Ind1 _ | Ind2 _ | Ind3 _ -> write_quad m (interp_ind m dst) value
  | _ -> raise Invalid_dest

exception Invalid_operands
(* Raise Invalid_operands if given invalid operand(s) for this instruction. *)
let validate_operands : ins -> unit = function
  | Imulq, [_; Reg _]
  | Sarq, [Imm _; _] | Sarq, [Reg Rcx; _]
  | Shlq, [Imm _; _] | Shlq, [Reg Rcx; _]
  | Shrq, [Imm _; _] | Shrq, [Reg Rcx; _]
  | Leaq, [Ind1 _; _] | Leaq, [Ind2 _; _] | Leaq, [Ind3 _; _]
  | Cmpq, [_; Ind1 _] | Cmpq, [_; Ind2 _] | Cmpq, [_; Ind3 _]
    -> ()
  | Imulq, _
  | Sarq, _
  | Shlq, _
  | Shrq, _
  | Leaq, _
    -> raise Invalid_operands
  | _ -> ()

(* Crack the instruction into possibly two or more instructions.
 * See the X86lite specification for details. *)
let rec crack : ins -> ins list = function
  | Pushq, [src] -> [Subq, [Imm (Lit 8L); Reg Rsp]; Movq, [src; Ind2 Rsp]]
  | Popq, [dst] -> [Movq, [Ind2 Rsp; dst]; Addq, [Imm (Lit 8L); Reg Rsp]]
  | Jmp, [src] -> [Movq, [src; Reg Rip]]
  | Callq, [src] -> crack (Pushq, [Reg Rip]) @ [Movq, [src; Reg Rip]]
  | Retq, [] -> crack (Popq, [Reg Rip])
  | insn -> [insn]
 
(* Evaluate the values of operands for computation. *)
(* Note: In the simulator, instruction operands will not contain labels. *)
let interp_operands (m: mach) : ins -> int64 list =
  let interp_val = interp_val m in
  let interp_ind = interp_ind m in
  function
  | Set _, _ -> []
  | Leaq, [ind; _] -> [interp_ind ind]
  | Movq, [src; _] -> [interp_val src]
  | Popq, _ -> []
  | J _, [src] -> [interp_val src]
  | _, operands -> List.map interp_val operands

exception Invalid_operator

(* Compute the instruction result. *)
let interp_opcode (m: mach) (op: opcode) (args: int64 list) : Int64_overflow.t = 
  let open Int64 in
  let open Int64_overflow in
  match op, args with

  | Negq, [dst] -> neg dst
  | Addq, [src; dst] -> add dst src
  | Subq, [src; dst] -> sub dst src
  | Imulq, [src; reg] -> mul reg src
  | Incq, [dst] -> succ dst
  | Decq, [dst] -> pred dst

  | Notq, [dst] -> lognot dst |> ok
  | Andq, [src; dst] -> logand dst src |> ok
  | Orq, [src; dst] -> logor dst src |> ok
  | Xorq, [src; dst] -> logxor dst src |> ok

  | Sarq, [amt; dst] -> shift_right dst ?>amt |> ok
  | Shlq, [amt; dst] -> shift_left dst ?>amt |> ok
  | Shrq, [amt; dst] -> shift_right_logical dst ?>amt |> ok
  | Set cc, [] -> (if interp_cnd m.flags cc then 1L else 0L) |> ok

  | Leaq, [ind] -> ind |> ok
  | Movq, [src] -> src |> ok

  | Cmpq, [src1; src2] -> sub src2 src1
  | J cc, [src] -> src |> ok

  | _ -> raise Invalid_operator

(* Update machine state with instruction results. *)
let ins_writeback (m: mach) : ins -> int64 -> unit =
  let set_dest_val = set_dest_val m in
  function
  | Negq, [dst] | Addq, [_; dst] | Subq, [_; dst] -> set_dest_val dst
  | Imulq, [_; reg] -> set_dest_val reg
  | Incq, [dst] | Decq, [dst] -> set_dest_val dst
  | Notq, [dst] | Andq, [_; dst]
  | Orq, [_; dst] | Xorq, [_; dst] -> set_dest_val dst
  | Sarq, [_; dst] | Shlq, [_; dst] | Shrq, [_; dst] -> set_dest_val dst
  | Set cc, [dst] -> fun b -> set_dest_val dst (Int64.logor b (Int64.logand (interp_val m dst) 0xFFFFFFFFFFFFFF00L))
  | Leaq, [_; dst] | Movq, [_; dst] -> set_dest_val dst
  | Cmpq, _ -> fun _ -> ()
  | J cc, _ -> if interp_cnd m.flags cc then set_dest_val (Reg Rip) else fun _ -> ()
  | _ -> raise Invalid_operator
  
  
  exception Invalid_argument
  (* Set the machine flags after an instruction.
  * See the X86lite specification for details. *)
  let set_flags (m: mach) (op: opcode) (args: quad list) (res: Int64_overflow.t) : unit =
  match op with
  | Notq | Set _ | Leaq | Movq | J _ -> ()
  | Sarq | Shlq | Shrq -> 
    begin
      match args with
      | [0L; _] -> ()
      | [amt; dst] ->
        begin
          match op with
          | Sarq -> begin
            m.flags.fs <- res.value < 0L;
            m.flags.fz <- res.value = 0L;
            if amt = 1L then m.flags.fo <- false
          end
          | Shlq -> begin
            m.flags.fs <- res.value < 0L;
            m.flags.fz <- res.value = 0L;
            if amt = 1L then m.flags.fo <- (dst < 0L) <> ((Int64.shift_left dst 1) < 0L)
          end
          | Shrq -> begin
            m.flags.fs <- res.value < 0L;
            if res.value = 0L then m.flags.fz <- true;
            if amt = 1L then m.flags.fo <- dst < 0L
          end
          | _ -> ()
        end
      | _ ->
        raise Invalid_argument
    end
  | _ -> 
    m.flags.fs <- res.value < 0L; 
    m.flags.fz <- res.value = 0L; 
    m.flags.fo <- res.overflow


(* Execute an instruction. *)
let step (m: mach) : unit =
  let rget, rset = rget m, rset m in

  let (op, oprnds) as insn = fetch_ins m (rget Rip) in
  validate_operands insn;
  
  let ops: ins list = crack (op, oprnds) in

  rset Rip (rget Rip +. ins_size);

  let set_flag : bool = match op with
    | Pushq | Popq | Jmp | Callq | Retq -> false
    | _ -> true
  in
  List.iter
    (fun (op, _ as insn) ->
      if !debug_simulator then print_endline @@ string_of_ins insn;
      let args = interp_operands m insn in
      let res = interp_opcode m op args in
      ins_writeback m insn @@ res.value;
      if set_flag then set_flags m op args res
    ) ops

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
            ; data_pos : quad              (* starting address of the data *)
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
     HINT: consider building a mapping from symboli Lbl to memory address

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let is_size (is: ins list): quad = 
  (* Map each instruction to int and sum up *)
  ?<(List.length is) *. ins_size
  (* List.fold_left (fun acc (op, oprnds) -> 
    acc +. ins_size *. ?<(List.length @@ crack @@ (op, oprnds))
  ) 0L is *)
let ds_size (ds: data list): quad = 
  (* Map each data to int and sum up *)
  List.fold_left (fun acc -> function
    | Asciz s -> acc +. 1L +. ?<(String.length s)
    | Quad _ -> acc +. 8L
  ) 0L ds

module StringMap = Map.Make(String)
let assemble (p:prog) : exec =
  (* Sort the segments of the program according to the asm type *)
  let p = List.stable_sort (fun {asm = a1} {asm = a2} -> 
    match a1, a2 with
    | Text _, Data _ -> -1
    | Data _, Text _ -> 1
    | _ -> 0
  ) p in
(* Create symbol table *)
  let symbol_table, text_end, data_begin = List.fold_left (fun (tbl, addr, sep) elem -> 
    let size = match elem.asm with
      | Text is -> is_size is
      | Data ds -> ds_size ds
    in 
    let sep = match sep, elem.asm with
    | -1L, Data _ -> addr
    | _ -> sep
    in
    if StringMap.mem elem.lbl tbl then 
      (* Note: No label of the same name is allowed in a single file. 
         We don't distinguish global and local labels. *)
      raise (Redefined_sym elem.lbl) 
    else 
      (StringMap.add elem.lbl addr tbl, addr +. size, sep)
  ) (StringMap.empty, mem_bot, -1L) p in
  (* When there's no data segment, date segment starts at the text_end *)
  let sep = if data_begin = -1L then text_end else data_begin in
  (* Replace the labels by Literals *)
  let p = List.map (fun elem -> 
    let resolve_oprnd = function
      | Imm Lbl l -> 
        begin
          match StringMap.find_opt l symbol_table with
          | Some addr -> Imm (Lit addr)
          | None -> raise (Undefined_sym l)
        end
      | Ind1 Lbl l ->
        begin
          match StringMap.find_opt l symbol_table with
          | Some addr -> Ind1 (Lit addr)
          | None -> raise (Undefined_sym l)
        end
      | Ind3 (Lbl l, reg) ->
        begin
          match StringMap.find_opt l symbol_table with
          | Some addr -> Ind3 (Lit addr, reg)
          | None -> raise (Undefined_sym l)
        end
      | x -> x
    in
    let resolve_ins = fun (op, oprnds)
      -> op, List.map resolve_oprnd oprnds
    in
    match elem.asm with
    | Text is -> {elem with asm = Text (List.map resolve_ins is)}
    | Data ds -> elem
  ) p in
  (* Separate the text and data segments *)
  let text, data = List.partition (fun {asm = a} -> match a with Text _ -> true | _ -> false) p in
  let text_seg = List.fold_left (
    fun acc {asm} -> match asm with 
    | Text is -> acc @ List.concat_map sbytes_of_ins is
    | Data _ -> raise Invalid_argument
  ) [] text
  in
  let data_seg = List.fold_left (
    fun acc {asm} -> match asm with 
    | Data ds -> acc @ List.concat_map sbytes_of_data ds
    | Text _ -> raise Invalid_argument
  ) [] data
  in
  (* Find the positions of the text and data segments *)
  let text_pos = mem_bot in
  let data_pos = sep in
  (* Find main label *)
  let entry = match StringMap.find_opt "main" symbol_table with
  | Some addr -> addr
  | None -> raise (Undefined_sym "main")
  in
  {entry; text_pos; data_pos; text_seg; data_seg}

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
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
  let mem = (Array.make mem_size (Byte '\x00')) in
  Array.blit (Array.of_list text_seg) 0 mem (map_addr_safe text_pos) (List.length text_seg);
  Array.blit (Array.of_list data_seg) 0 mem (map_addr_safe data_pos) (List.length data_seg);
  let regs = Array.make nregs 0L in
  regs.(rind Rip) <- entry;
  regs.(rind Rsp) <- Int64.sub mem_top 8L;
  let m = { 
    flags = {fo = false; fs = false; fz = false};
    regs = regs;
    mem = mem
  } in
  write_quad m (rget m Rsp) exit_addr;
  m
  
