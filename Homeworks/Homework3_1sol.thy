chapter \<open>Homework 3\<close>
theory Homework3_1sol
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
  
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<times> state" where
  "aval (N v) s = (v,s)"
| "aval (V x) s = (s x, s)"  
| "aval (Inc x) s = (s x + 1, s( x:= s x + 1))"
| "aval (Plus a1 a2) s = (let (v1,s) = aval a1 s; (v2,s) = aval a2 s in (v1+v2,s)) "
  
(* Like in the tutorial, it was important to change both the state, and return the incremented value.

  The most frequent mistake here was to not change the state, making Inc x just an alias for
  Plus (V x) (N 1). Then, of course, the compiler was straightforward, and the STORE instruction 
  was actually not needed. I still gave 3 points for such solutions.
*)
  
  
  
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

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
apply(induction a arbitrary: s) (** The only difference to the original proof 
  is that you need to generalize over the state s, as this is changed during execution. *)
apply simp_all
done
  
  
section \<open>Compiling with Side-Effect\<close>
  
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
  
fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Inc x) = [LOAD x, LOADI 1, ADD, STORE x, LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"
  
(** The code for Inc will add one, store the result in variable x, and immediately load it from x.
  This changes both the state and places the incremented result on top of the stack.
*)


theorem exec_comp:
  "aval a s = (v,s') \<Longrightarrow> exec (comp a) (s,stk) = (s',v#stk)"
  apply (induction a arbitrary: v s s' stk)
  apply (auto split: prod.splits)
  done
    
(** You have to generalize over all variables that will change during execution.
  The split: prod.splits takes care of the remaining 
  "case aval a1 s of (v1, s) \<Rightarrow> \<dots>" (and, similar for a2, v2)
 *)    
      
end
