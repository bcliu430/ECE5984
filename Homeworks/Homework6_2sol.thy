theory Homework6_2sol
imports Main "~~/src/HOL/Eisbach/Eisbach"
begin

(*
  We extend IMP by arrays.
  Each variable is now a list of integers, and variable 
  access takes an additional index.
*)

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val list"

datatype aexp = N int | V vname aexp | Plus aexp aexp

(*
  Unfortunately, array access may be out of bounds.
  Thus, we model evaluation of expressions as partial function,
  returning None if array index is out of bounds.
*)

(* Give case for variable! Note: 
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
"aval (Plus a\<^sub>1 a\<^sub>2) s = (
  case aval a\<^sub>1 s of 
    None \<Rightarrow> None 
  | Some r1 \<Rightarrow> (
      case aval a\<^sub>2 s of
        None \<Rightarrow> None
      | Some r2 \<Rightarrow> Some (r1+r2)))
      "

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

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool option" where
"bval (Bc v) s = Some v" |
"bval (Not b) s = (case bval b s of None \<Rightarrow> None | Some b \<Rightarrow> Some (\<not>b))" |
(*<*)
"bval (And b\<^sub>1 b\<^sub>2) s = (case bval b\<^sub>1 s of 
    None \<Rightarrow> None 
  | Some r1 \<Rightarrow> (case bval b\<^sub>2 s of
      None \<Rightarrow> None
    | Some r2 \<Rightarrow> Some (r1 \<and> r2))
  )" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (case aval a\<^sub>1 s of 
    None \<Rightarrow> None
  | Some r1 \<Rightarrow> (case aval a\<^sub>2 s of
      None \<Rightarrow> None
    | Some r2 \<Rightarrow> Some (r1<r2)))"
(*>*)    

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
(*<*)
IfTrue: "\<lbrakk> bval b s = Some True;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> bval b s = Some False;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "bval b s = Some False \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
"\<lbrakk> bval b s\<^sub>1 = Some True;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"
(*>*)

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

(* Proof should not change ... *)
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
  You will probably have to perform an Isar-proof here, or try to fiddle 
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
proof (induction arbitrary: u rule: big_step.induct)
  case (Skip s)
  then show ?case by auto
next
  case (Assign a s v i idx x)
  then show ?case by auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by blast
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  from IfTrue.prems IfTrue.hyps(1) IfTrue.IH
  show ?case by auto
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  from IfFalse.prems IfFalse.hyps(1) IfFalse.IH
  show ?case by auto
next
  case (WhileFalse b s c)
  then show ?case by auto
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  from WhileTrue.prems \<open>bval b s\<^sub>1 = Some True\<close> WhileTrue.IH(1) have
    "(WHILE b DO c, s\<^sub>2) \<Rightarrow> u" by auto
  with WhileTrue.IH(2) show ?case by simp
qed


(*  
  Write a program that sums up the elements from l..<h of array a, and
  returns the result in r.
  
  Hint:
    r=0;
    while (l<h) r+=a[l++];

*)


abbreviation "array_sum \<equiv> 
  ''r'' ::= N 0;;
  WHILE Less (V0 ''l'') (V0 ''h'') DO (
    ''r'' ::= Plus (V0 ''r'') (V ''a'' (V0 ''l''));;
    ''l'' ::= Plus (V0 ''l'') (N 1)
  )"

(* Use automatic big-step derivation to test your program! 
  Note that the BigSteps method will fail to generate a derivation if
  execution gets stuck b/c index-out-of-bounds
*)  
  
schematic_goal "(array_sum,<''l'':=[1], ''h'':=[5], ''a'':=[100,1,2,3,4,200,300]>) \<Rightarrow> ?s"
  by BigSteps

(*
  Write another program that sums up only the elements >5 of array a, 
  in between l..<h, and returns the result in r.
  Test your program!
  
  Hint: Start with the array_sum program and extend it.
*)
  
abbreviation "array_sum_gt5 \<equiv> 
  ''r'' ::= N 0;;
  WHILE Less (V0 ''l'') (V0 ''h'') DO (
    IF Less (N 5) (V ''a'' (V0 ''l'')) THEN
      ''r'' ::= Plus (V0 ''r'') (V ''a'' (V0 ''l''))
    ELSE SKIP;;  
    ''l'' ::= Plus (V0 ''l'') (N 1)
  )"

  
schematic_goal "(array_sum_gt5,<''l'':=[1], ''h'':=[5], ''a'':=[100,1,7,13,4,200,300]>) \<Rightarrow> ?s"
  by BigSteps
  
  
end
