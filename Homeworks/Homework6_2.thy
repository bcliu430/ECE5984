theory Homework6_2
imports Main "~~/src/HOL/Eisbach/Eisbach"
begin

(*
  ISSUED: Wednesday, October 25
  DUE: Wednesday, November 1, 11:59pm
  POINTS: 5
*)


(*
  We extend IMP by arrays.
  Each variable is now a list of integers, and variable 
  access takes an additional index.
  
  Hint: Use the standard IMP theories as a template
*)

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val list"

datatype aexp = 
    N int 
  | V vname aexp     (* x[i], i.e., array x at index i, where i is an arithmetic expression *)
  | Plus aexp aexp

(*
  Unfortunately, array access may be out of bounds.
  Thus, we model evaluation of expressions as partial function,
  returning None if array index is out of bounds.
*)

(*
  Complete the following function definition.
  Note:
    l!i selects the ith element of list l, 
    and nat converts an int to a nat.
*)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val option" where
"aval (N n) s = Some n" |
"aval (V x i) s = (
  case aval i s of 
    None \<Rightarrow> None 
  | Some i \<Rightarrow> (
      if 0\<le>i \<and> nat i<length (s x) then 
        Some (s x ! nat i) 
      else None)
  )" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = undefined" (* Insert meaningful equation here! *)

text {* A little syntax magic to write larger states compactly: *}

(* All variables are arrays of length 1, initialized by zero.
  This simulates the behaviour of original IMP.
*)
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. [0]"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

lemma null_state_app[simp]: "<> x = [0]" by (auto simp: null_state_def)

abbreviation "V0 x \<equiv> V x (N 0)" (* Abbreviation for x[0]. 
  Again, models the behaviour of original IMP. *)

(* Test cases *)  
value "aval (Plus (V ''x'' (V0 ''y'')) (V ''x'' (N 1))) <''x'':=[1,2,3], ''y'':=[2]> = Some 5"
value "aval (Plus (N 2) (V ''x'' (N 2))) <''x'':=[1,2]> = None" (* Index out of bounds *)


datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp


(* Complete the following function definition!   *)
fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool option" where
"bval (Bc v) s = Some v" |
"bval (Not b) s = (case bval b s of None \<Rightarrow> None | Some b \<Rightarrow> Some (\<not>b))" |
"bval (And b\<^sub>1 b\<^sub>2) s = undefined" |
"bval (Less a\<^sub>1 a\<^sub>2) s = undefined"

datatype
  com = SKIP 
      | Assign vname aexp aexp  ("_[_] ::= _" [1000,900, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)

(* Abbreviation to get x ::= e syntax, as abbreviation for x[N 0] ::= e *)
abbreviation Assign0 ("_ ::= _" [1000, 61] 61) where 
  "x ::= v \<equiv> (x[N 0] ::= v)"

(*
  Give Skip,Assign,Seq rule. 
  
  The big-step semantics shall get stuck in case of array-index-out-of-bounds.
  That is, the preconditions of the rules assume that the indexes are in bounds,
  and that aval/bval return Some result.
  
  Note: l[i:=v] replaces ith element of list l by v
*)  
inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "\<lbrakk> 
  aval a s = Some v; 
  aval i s = Some idx; 
  0\<le>idx; 
  nat idx<length (s x) \<rbrakk> 
\<Longrightarrow> (x[i] ::= a,s) \<Rightarrow> s(x := ((s x)[nat idx := v]))" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
(* add reasonable preconditions for the following rules! *)
IfTrue: "\<lbrakk> undefined \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> undefined \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<lbrakk> undefined \<rbrakk> \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue: "\<lbrakk> undefined \<rbrakk> \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

(* Setup for program derivation *)
method If = (rule IfTrue, (simp;fail)) | (rule IfFalse, (simp;fail))
method While = (rule WhileTrue, (simp;fail)) | (rule WhileFalse, (simp;fail))
method BigStep = simp?; ((rule Skip Assign Seq) | If | While)
method BigSteps = BigStep+


(* Automation setup *)
declare big_step.intros [intro]

lemmas big_step_induct = big_step.induct[split_format(complete)]

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"

inductive_cases AssignE[elim!]: "(x[i] ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE

(* This proof should not change ... *)
lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(c1, s) \<Rightarrow> s1" and
    c2: "(c2, s1) \<Rightarrow> s2" and
    c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  -- "The other direction is analogous"
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"
  thus "(c1;; c2;; c3, s) \<Rightarrow> s'" by auto
qed

(*
  Prove that the big-step semantics is deterministic.

  The proof is analogous to its counterpart in BigStep.thy. 
  However, you will probably have to perform an Isar-proof here, or try to fiddle 
  through with sledgehammer.
  The problem is that the induction generates goals like
  
  \<And>b s c\<^sub>1 t c\<^sub>2 u.
     \<lbrakk> bval b s = Some True; 
      (c\<^sub>1, s) \<Rightarrow> t; 
      \<And>u. (c\<^sub>1, s) \<Rightarrow> u \<Longrightarrow> u = t; 
      (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> u
     \<rbrakk>
     \<Longrightarrow> u = t  

  This will crash the simplifier, which uses the 2nd and 3rd premise to rewrite with t=t.   
  In the Isar-proof, try to only use the necessary premises \<dots>
*)

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  oops

(*  
  Write a program that sums up the elements from indexes l..<h of array a, and
  returns the result in r.
  
  Hint:
    r=0;
    while (l<h) r+=a[l++];

*)


abbreviation "array_sum \<equiv> SKIP"

(* Use automatic big-step derivation to test your program! 
  Test for various test cases, in particular making sure you have no off-by-one errors!

  Note that the BigSteps method will fail to generate a derivation if
  execution gets stuck b/c index-out-of-bounds
*)  
  
schematic_goal "(array_sum,<''l'':=[1], ''h'':=[5], ''a'':=[100,1,2,3,4,200,300]>) \<Rightarrow> ?s"
  by BigSteps

(*
  Write another program that sums up the elements in between indexes l..<h of array a,
  but ignores elements with a value less than or equal to 5.
  The result must be returned in variable r.
  Test your program!
  
  Hint: Start with the array_sum program and extend it.
*)
  
abbreviation "array_sum_gt5 \<equiv> SKIP"
  
schematic_goal "(array_sum_gt5,<''l'':=[1], ''h'':=[5], ''a'':=[100,1,7,13,4,200,300]>) \<Rightarrow> ?s"
  by BigSteps
  
  
end
