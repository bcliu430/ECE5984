theory Homework4_1
imports "../IMP/AExp" (* Replace by your path to AExp *)
begin

  (*
    ISSUED: Wednesday, October 11
    DUE: Wednesday, October 18, 11:59pm
    POINTS: 5
  *)

(*
  The objective of this homework is to compile to a register machine.

  Hint: To solve this homework, it is best to have ASM.thy 
    open for reference in another window!

*)  
  
(* We assume we have an unlimited amount of registers, register names are 
  just natural numbers *)
type_synonym reg = nat
  
(* Instructions of our register machine *)  
datatype inst = 
    MOVI val reg      (* MOVI v r  -- move constant (immediate value) v to register r *)
  | LOAD vname reg    (* LOAD x r  -- load variable x to register r *)
  | ADD reg reg       (* ADD r1 r2 -- add values contained in registers r1 and r2, place the result in r1 *)

(* The state of our machine's register bank is described by a function mapping
  register names to values.
*)    
type_synonym rstate = "reg \<Rightarrow> val"

(*
  Specify the semantics for executing a single instruction! 
  Note: As there is no store instruction, the variable state is not modified.
*)  
fun exec1 :: "inst \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec1 _ _ _ = undefined"

(*
  Specify the semantics of executing a list of instructions!
*)  
fun exec :: "inst list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec _ _ _ = undefined"
  
lemma exec_append[simp]:
  "exec (is1@is2) s t = exec is2 s (exec is1 s t)"
  (* Prove that! *)
  sorry

(*
  In order to compile an arithmetic expression, the intermediate results must be assigned 
  to intermediate registers, and it must be ensured that fresh intermediate registers are used.

  For example, when compiling a1+a2, we first generate code that compiles a1 
  and places the result in some register r1, then we generate code to compile a2,
  place the result in some register r2, and finally add the two registers, the 
  final result going to register r1. 
  However, we must ensure that the code generated for a2 does not overwrite register r1.
  
  We use the following strategy: We pass an additional parameter r to the compiler,
  which is the register that should contain the result value. Additionally, all 
  registers less than r must not be changed by the generated code.

  That is, to compile an expression a1 + a2 to register r, we do the following:
    1. generate code that evaluates a1 to register r, not changing registers <r
    2. generate code that evaluates a2 to register r+1, not changing registers <r+1 
        (in particular, register r is not changed!)
    3. add register r and r+1, placing the result in register r


*)  
  
hide_const (open) comp  
  
(* Implement the compiler! *)  
fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> inst list" where
  "comp _ _ = undefined"
  
(* Test case *)
  
value "comp (Plus (Plus (N 3) (V ''x'')) (Plus (N 1) (V ''y''))) 1 = 
[MOVI 3 (Suc 0), LOAD ''x'' (Suc (Suc 0)), ADD (Suc 0) (Suc (Suc 0)), MOVI 1 (Suc (Suc 0)),
  LOAD ''y'' (Suc (Suc (Suc 0))), ADD (Suc (Suc 0)) (Suc (Suc (Suc 0))), ADD (Suc 0) (Suc (Suc 0))]
"
  
  
(* Show that the produced code does not change registers less than r! *)  
lemma comp_preserves_regs[simp]: "r'<r \<Longrightarrow> exec (comp a r) s t r' = t r'"
  sorry
  
(* Show that the produced code places the correct result in register r! *)
lemma comp_correct: "exec (comp a r) s t r = aval a s"
  sorry

  

end
