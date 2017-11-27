(* Author: Peter Lammich *)

theory VCG 
imports Hoare_Examples "~~/src/HOL/Library/Rewrite"
begin

text \<open>We annotate the invariant to the WHILE-loop.
  This annotation does not actually change the syntax tree or semantics.
\<close>

definition AWHILE :: "assn \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" ("(INVAR _ WHILE _/ DO _)"  [0, 0, 61] 61)
  where "INVAR I WHILE b DO c \<equiv> WHILE b DO c"

lemma annot_invar: "WHILE b DO c = INVAR I WHILE b DO c" by (simp add: AWHILE_def)
  
lemma awhile_rule:
  assumes "\<Turnstile> {R} c {P}"
  assumes "\<And>s. \<lbrakk>P s; bval b s\<rbrakk> \<Longrightarrow> R s"
  assumes "\<And>s. \<lbrakk>P s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q s"
  shows "\<Turnstile> {P} INVAR P WHILE b DO c {Q}"
  unfolding AWHILE_def by (rule while_rule[OF assms])

lemmas vcg_rules = skip_rule assign_rule seq_rule if_rule awhile_rule

(* A first test *)
lemma "\<Turnstile> {\<lambda>s. s ''x'' = n} ''y'' ::= N 0;; wsum {\<lambda>s. s ''y'' = sum n}"
  apply (rewrite annot_invar[where I="\<lambda>s. (s ''y'' = sum n - sum(s ''x''))"])
  apply (rule conseq_pre_rule)
  apply (rule vcg_rules)
  apply (rule vcg_rules)
  apply (rule vcg_rules)
  apply (rule vcg_rules)
  apply (rule vcg_rules)
  apply simp
  apply simp
  apply (rule vcg_rules)
  apply simp
  done  
    
lemma "\<Turnstile> {\<lambda>s. s ''x'' = n} ''y'' ::= N 0;; wsum {\<lambda>s. s ''y'' = sum n}"
  apply (rewrite annot_invar[where I="\<lambda>s. (s ''y'' = sum n - sum(s ''x''))"])
  apply (rule conseq_pre_rule)
  apply (rule vcg_rules | simp)+
  done

  
(* Automating the VCG *)  
method vcg_step = rule vcg_rules | clarsimp
method vcg = rule conseq_pre_rule, vcg_step+


(* Examples *)

(* For simple invariants, everything can be done automatically *)
lemma "\<Turnstile> {\<lambda>s. s ''x'' = n} ''y'' ::= N 0;; wsum {\<lambda>s. s ''y'' = sum n}"
  apply (rewrite annot_invar[where I="\<lambda>s. (s ''y'' = sum n - sum(s ''x''))"])
  by vcg

(* If invariants get more complicated, automatic proof may not scale or be 
  hard to develop and read *)  
  
lemma "\<Turnstile> {\<lambda>s. s ''x'' = x\<^sub>0 \<and> x\<^sub>0\<ge>0} DerTreeExample.square { \<lambda>s. s ''a'' = x\<^sub>0\<^sup>2 }"
  apply (rewrite annot_invar[where I="\<lambda>s. 
    let c = x\<^sub>0-s ''x'' in 
       0\<le>s ''x'' \<and> 0\<le>c \<and> s ''b'' = 1+2*c \<and> s ''a'' = c\<^sup>2"])
  supply power2_eq_square[simp] algebra_simps[simp]
  apply vcg
  done
  
(* More manual proof. Better readable and simpler to write *)  
  
lemma "\<Turnstile> {\<lambda>s. s ''x'' = x\<^sub>0 \<and> x\<^sub>0\<ge>0} DerTreeExample.square { \<lambda>s. s ''a'' = x\<^sub>0\<^sup>2 }"
proof -
  define I where "I x a b \<equiv> let c=x\<^sub>0-x in 0\<le>x\<^sub>0 \<and> 0\<le>x \<and> 0\<le>c \<and> b=1+2*c \<and> a=c\<^sup>2"
    for x a b

  have [simp]: "I (x-1) (a+b) (b+2)" if "I x a b" "0<x" for x a b
    using that unfolding I_def by (auto simp: algebra_simps power2_eq_square)

  have [simp]: "a=x\<^sub>0\<^sup>2" if "I x a b" "\<not>0<x" for x a b
    using that unfolding I_def by (auto simp: algebra_simps power2_eq_square)

  have [simp]: "I x\<^sub>0 0 1" if "0\<le>x\<^sub>0"
    using that unfolding I_def by (auto simp: algebra_simps power2_eq_square)
      
  show ?thesis
    apply (rewrite annot_invar[where I="\<lambda>s. I (s ''x'') (s ''a'') (s ''b'')"])
    apply vcg
    done
      
qed    
  
  

(* More contrieved example *)
abbreviation "IMP_div \<equiv> 
  ''q'' ::= N 0;;
  ''c'' ::= N 0;;
  WHILE Not (Less ((V ''x'')) (V ''c'')) DO (
    ''c'' ::= Plus (V ''c'') (V ''y'');;
    ''q'' ::= Plus (V ''q'') (N 1)
  );;
  ''q'' ::= Plus (V ''q'') (N (-1))
"

(* As alternative to define the invariants inside the proof, we can also
  use a definition, and prove lemmas.
*)

definition div_invar :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" 
  where "div_invar x y c q \<equiv> c = q*y \<and> c \<le> x+y \<and> x>0 \<and> y>0 \<and> q\<ge>0"

lemma div_invar1: "\<lbrakk>div_invar x y c q; \<not>x<c \<rbrakk> \<Longrightarrow> div_invar x y (c+y) (q+1)" 
  unfolding div_invar_def 
  by (auto simp: algebra_simps)

lemma div_invar2: "\<lbrakk>div_invar x y c q; x < c \<rbrakk> \<Longrightarrow> q - 1 = x div y"
  unfolding div_invar_def 
  apply (auto simp: algebra_simps)
  by (smt Divides.pos_mod_sign cancel_div_mod_rules(2) div_add_self2 mult.commute nonzero_mult_div_cancel_right zdiv_mono1)

lemma div_invar3: "\<lbrakk>x>0; y>0\<rbrakk> \<Longrightarrow> div_invar x y 0 0" 
  unfolding div_invar_def 
  by (auto simp: algebra_simps)

lemma "\<Turnstile> {\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> x>0 \<and> y>0} IMP_div {\<lambda>s. s ''q'' = x div y}"  
  apply (rewrite annot_invar[where I="\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> div_invar x y (s ''c'') (s ''q'')"])
  supply div_invar1[simp]
  supply div_invar2[simp]
  supply div_invar3[simp]
  apply vcg  
  done
  
  
  
  
  
end
