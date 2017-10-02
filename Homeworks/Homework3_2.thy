chapter \<open>Homework 3\<close>
theory Homework3_2
imports 
  Main 
  "../IMP/AExp" (* Note: Replace this by your path to AExp *)
begin
  
  (*
    This file is intended to be viewed within the Isabelle/jEdit IDE.
    In a standard text-editor, it is pretty unreadable!
  *)

  (*
    HOMEWORK #3 PART II/II
    RELEASED: Tue, Aug 26 2017
    DUE:      Wed, Feb 4, 2017, 11:59pm

    To be submitted via canvas.
  *)
  

section \<open>General Hints\<close>  
(*
  The best way to work on this homework is to fill in the missing gaps in this file.

  Try to go for simple function definitions, as simple definitions mean simple proofs!
  In particular, do not go for a more complicated definition only b/c it may be more efficient!

*)  
  

section \<open>Absence of Stack-Overflows\<close>
  
text \<open>Model a stack machine that explicitly returns @{const \<open>None\<close>} 
  on stack underflow, and @{term \<open>Some stk\<close>} otherwise.
\<close>  
  
datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1  :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where 
  "exec1 (LOADI n) _ stk  =  Some (n # stk)"
  (* Add the other equations! *)
  

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec _ _ _ = undefined"
(* Hint: Use case distinction to distinguish between None and Some stk. *)



lemma exec_append[simp]:
  "exec (is1@is2) s stk = (case exec is1 s stk of None \<Rightarrow> None | Some stk \<Rightarrow> exec is2 s stk)"
  oops
  
(* The compiler remains unchanged *)    
fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

(* Prove that executing a compiled program actually returns the correct value.
  In particular, it does not return None, which would mean stack underflow.
*)
theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
  (* The correctness proof is slightly changed *)
  oops
    
      
end
