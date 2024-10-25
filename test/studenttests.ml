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
    failwith "Should have raised Not_an_ins"
  with 
    | Not_an_ins -> ()
    | _ -> failwith "Should have raised Not_an_ins"

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
    
  ]);

] 
