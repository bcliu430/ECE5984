chapter \<open>Homework 3\<close>
theory Homework3_2sol
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
| "exec1 (LOAD x) s stk  =  Some (s(x) # stk)"
| "exec1 ADD _ (a#b#stk) = Some ((a+b)#stk)"
| "exec1 ADD _ _ = None"   
  
(** The definition was straightforward, just inserting Some, and making the 
  catch-all equation return None instead of undefined. 
*)  
  
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk = (
  case exec1 i s stk of    (** We first execute instruction i *)
    None \<Rightarrow> None           (** If this fails, we return None*)  
  | Some stk \<Rightarrow> exec is s stk)" (** Otherwise, we call the new stack stk 
      (hiding the binding of the old stack, which is intentional here, as 
        it makes it impossible to accidentally access the old stack)  
      and execute the remaining instructions on the new stack.
  *)
  
lemma exec_append[simp]:
  "exec (is1@is2) s stk = (case exec is1 s stk of None \<Rightarrow> None | Some stk \<Rightarrow> exec is2 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto split: option.splits)
done
  
fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"
  
theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
apply(induction a arbitrary: stk)
apply (auto)
done
  
(** Actually, the correctness proof did not change at all for this sample solution -- 
  In some solutions, you might have to insert a split: option.splits.
*)  
  
    
      
end
