open Util.Assert
open X86
open Sim.Simulator
open Gradedtests
open Asm 
(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)


let test_my =
  let bin = [
    InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    ] 
  
  in 

  let asm =  [gtext "main"
  [ 
    Movq,  [~$42; ~%Rax]];
  ] in 

  (assert_eqf (fun() ->  (assemble asm).text_seg) bin )

 
let mov_ri =
 test_machine
 [
 InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 ]

let read_machine = test_machine
  ( sbytes_of_int64 0xdeadbeefdeadbeefL
  @ sbytes_of_int64 0xbeefdeadbeefdeadL
  )

let write_machine = {read_machine with
    mem = Array.copy read_machine.mem
}

let test_fetch_ins_invalid = fun () ->
  try ignore (fetchins read_machine mem_bot);
    failwith "Should have raised Invalid_ins"
  with 
    | Invalid_ins -> ()
    | _ -> failwith "Should have raised Invalid_ins"

let mod_prog a b = [
  text "mod"
    [ Cmpq,  [~%Rdi; ~%Rsi]
    ; J Gt,  [~$$"exit"]
    ; Subq,  [~%Rsi; ~%Rdi]
    ; Callq, [~$$"mod"]
    ; Retq,  []
    ]
; text "exit"
    [ Movq,  [~%Rdi; ~%Rax]
    ; Retq,  [] 
    ]
; gtext "main"
    [ Movq,  [~$a; ~%Rdi]
    ; Movq,  [~$b; ~%Rsi]
    ; Callq, [~$$"mod"]
    ; Retq,  []
    ]
]

let gcd_prog a b = [
  text "mod"
    [ Cmpq,  [~%Rdi; ~%Rsi]
    ; J Gt,  [~$$"mod_exit"]
    ; Subq,  [~%Rsi; ~%Rdi]
    ; Callq, [~$$"mod"]
    ; Retq,  []
    ]
; text "mod_exit"
    [ Movq,  [~%Rdi; ~%Rax]
    ; Retq,  [] 
    ]
; text "gcd"
    [ Cmpq,  [~$0; ~%Rsi]
    ; J Eq,  [~$$"gcd_exit"]
    ; Callq, [~$$"mod"]
    ; Movq,  [~%Rsi; ~%Rdi]
    ; Movq,  [~%Rax; ~%Rsi]
    ; Callq, [~$$"gcd"]
    ; Retq,  []
    ]
; text "gcd_exit"
    [ Movq,  [~%Rdi; ~%Rax]
    ; Retq,  [] 
    ]
; gtext "main"
    [ Movq,  [~$a; ~%Rdi]
    ; Movq,  [~$b; ~%Rsi]
    ; Callq, [~$$"gcd"]
    ; Retq,  []
    ]
]

(* function gcd(a, b)
    if b = 0
        return a
    else
        c = a mod b
        return gcd(b, c) *)

let provided_tests : suite = [
  
  Test ("My Tests", [
    ("assert", test_my)
  ]);

  Test ("Student: Read Write Quad Tests", [
    ("read_quad_1", assert_eq (readquad read_machine mem_bot) 0xdeadbeefdeadbeefL);
    ("read_quad_2", assert_eq (readquad read_machine (mem_bot +. 8L)) 0xbeefdeadbeefdeadL);
    ("read_quad_3", assert_eq (readquad read_machine (mem_bot +. 4L)) 0xbeefdeaddeadbeefL);
    ("write_quad_1", assert_eq ( writequad write_machine (mem_bot +. 4L) 0xfeedadeafbeebeefL
                               ; readquad write_machine (mem_bot +. 4L)) 0xfeedadeafbeebeefL);
  ]);

  Test ("Student: Fetch Instruction Invalid", [
    ("fetch_ins_invalid", test_fetch_ins_invalid)
  ]);

  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
    ("mod", program_test (mod_prog 8 3) 2L);
    ("gcd", program_test (gcd_prog 24 16) 8L);
  ]);

] 