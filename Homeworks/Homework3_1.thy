chapter \<open>Homework 3\<close>
theory Homework3_1
imports Main
begin
  
  (*
    This file is intended to be viewed within the Isabelle/jEdit IDE.
    In a standard text-editor, it is pretty unreadable!
  *)

  (*
    HOMEWORK #3 PART I/II
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
  

section \<open>Arithmetic Expressions with Side-Effects\<close>
  
text \<open>Model arithmetic expressions that contain 
  constants, variables, addition, and the prefix \<open>++\<close>-operator known from
  C++ and Java. The expression \<open>++x\<close> where \<open>x\<close> must be a variable, 
  increments \<open>x\<close> and evaluates to the incremented value of \<open>x\<close>.
\<close>  
type_synonym vname = string
type_synonym val = int  
type_synonym state = "vname \<Rightarrow> val"
  
text {* A little syntax magic to write larger states compactly: *}

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"
  
  
datatype aexp = N val | V vname | Inc vname | Plus aexp aexp
  
(* Evaluation now returns a pair of the value and the new state *)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<times> state" where
  "aval _ _ = undefined" (* Replace by meaningful equations *)
  
(* The optimizer remains unchanged. There is no optimization for pre-increment. *)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval (Plus a1 a2) s"
apply(induction a1 a2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Inc x) = Inc x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"

(* Anyway, the proof will (slightly) change. Do the proof! *)
theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
  oops
  
  
section \<open>Compiling with Side-Effect\<close>

(* We use the stack-machine with \<open>STORE x\<close> instruction from the tutorial:*)  
  
datatype instr = LOADI val | LOAD vname | STORE vname | ADD
type_synonym stack = "val list"

fun exec1  :: "instr \<Rightarrow> (state \<times> stack) \<Rightarrow> state \<times> stack" where 
  "exec1 (LOADI n) (s, stk)  =  (s, n # stk)"
| "exec1 (LOAD x) (s, stk)  =  (s, s(x) # stk)"
| "exec1 (STORE x) (s, a#stk) = (s(x:=a), stk)"
| "exec1 (STORE _) _ = undefined"
| "exec1 ADD (s, a#b#stk) = (s,(a+b)#stk)"
| "exec1 ADD _ = undefined"   
  
  
fun exec :: "instr list \<Rightarrow> (state \<times> stack) \<Rightarrow> state \<times> stack" where
"exec [] sxstk = sxstk" |
"exec (i#is) sxstk = exec is (exec1 i sxstk)"

  
lemma exec_append[simp]:
  "exec (is1@is2) sxstk = exec is2 (exec is1 sxstk)"
apply(induction is1 arbitrary: sxstk)
apply (auto)
done
  
hide_const (open) comp  
  
(* Implement a compiler! Hint: This is quite similar to the tutorial! *)  
fun comp :: "aexp \<Rightarrow> instr list" where
"comp _ = undefined"

(* Prove it correct! Hint: The proof is quite similar to the tutorial! *)
theorem exec_comp:
  "aval a s = (v,s') \<Longrightarrow> exec (comp a) (s,stk) = (s',v#stk)"
  oops
    
    
      
end
