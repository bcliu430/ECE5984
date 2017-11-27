(* Author: Tobias Nipkow. Peter Lammich. *)

section "Hoare Logic"

theory Hoare imports Big_Step begin

subsection "Hoare Logic for Partial Correctness"

type_synonym assn = "state \<Rightarrow> bool"

definition
hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile> {P}c{Q} = (\<forall>s t. P s \<and> (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

lemma hoare_validI: 
  assumes "\<And>s t. \<lbrakk> P s; (c,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> Q t"
  shows "\<Turnstile> {P}c{Q}"
  using assms by (auto simp: hoare_valid_def)

lemma conseq_rule: 
  assumes "\<And>s. P s \<Longrightarrow> P' s"
  assumes "\<Turnstile> {P'} c {Q'}"
  assumes "\<And>s. Q' s \<Longrightarrow> Q s"
  shows "\<Turnstile> {P} c {Q}"
  using assms by (auto simp: hoare_valid_def)

(* One-sided versions of the consequence rule *)  
lemma conseq_pre_rule: 
  assumes "\<Turnstile> {P'} c {Q}"
  assumes "\<And>s. P s \<Longrightarrow> P' s"
  shows "\<Turnstile> {P} c {Q}"
  using assms using conseq_rule by blast

lemma conseq_post_rule: 
  assumes "\<And>s. Q s \<Longrightarrow> Q' s"
  assumes "\<Turnstile> {P} c {Q}"
  shows "\<Turnstile> {P} c {Q'}"
  using assms using conseq_rule by blast

lemma skip_rule: "\<Turnstile> {P} SKIP {P}"
  by (auto simp: hoare_valid_def)

lemma assign_rule: "\<Turnstile> {\<lambda>s. P(s(x := aval a s))} x::=a {P}"
  by (auto simp: hoare_valid_def)

lemma basic_seq_rule:
  assumes "\<Turnstile> {P} c\<^sub>1 {Q}" "\<Turnstile> {Q} c\<^sub>2 {R}"
  shows "\<Turnstile> {P} c\<^sub>1;;c\<^sub>2 {R}"
  using assms by (auto simp: hoare_valid_def)
  
lemma if_rule:  
  assumes "\<Turnstile> {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q}" "\<Turnstile> {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q}"
  shows "\<Turnstile> {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"
  using assms by (auto simp: hoare_valid_def)

lemma basic_while_rule:
  assumes "\<Turnstile> {\<lambda>s. P s \<and> bval b s} c {P}"
  shows "\<Turnstile> {P} WHILE b DO c {\<lambda>s. P s \<and> \<not> bval b s}"
proof (rule hoare_validI)  
  fix s t
  assume "(WHILE b DO c, s) \<Rightarrow> t" "P s" 
  then show "P t \<and> \<not> bval b t"
  proof (induction "WHILE b DO c" s t rule: big_step_induct)
    case (WhileFalse s)
    then show ?case by simp
  next
    case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
    note IH = \<open>P s\<^sub>2 \<Longrightarrow> P s\<^sub>3 \<and> \<not> bval b s\<^sub>3\<close>
    
    from \<open>P s\<^sub>1\<close> \<open>bval b s\<^sub>1\<close> \<open>(c, s\<^sub>1) \<Rightarrow> s\<^sub>2\<close> \<open>\<Turnstile> {\<lambda>s. P s \<and> bval b s} c {P}\<close> have "P s\<^sub>2"
      unfolding hoare_valid_def by auto
    with IH show "P s\<^sub>3 \<and> \<not> bval b s\<^sub>3" .
  qed
qed  


text \<open>We swap the premises of the sequence rule, as our 
  verification condition generator will work on sequences 
  from right to left.\<close>
lemma seq_rule:
  assumes "\<Turnstile> {Q} c\<^sub>2 {R}" "\<Turnstile> {P} c\<^sub>1 {Q}"
  shows "\<Turnstile> {P} c\<^sub>1;;c\<^sub>2 {R}"
  using basic_seq_rule assms by blast


text \<open>We combine the while-rule with a consequence rule, to
  make it more usable in verification condition generation\<close>

(* Explicit backwards derivation *)
lemma while_rule:
  assumes "\<Turnstile> {R} c {P}"
  assumes "\<And>s. \<lbrakk>P s; bval b s\<rbrakk> \<Longrightarrow> R s"
  assumes "\<And>s. \<lbrakk>P s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q s"
  shows "\<Turnstile> {P} WHILE b DO c {Q}"
  apply (rule conseq_post_rule[where Q="\<lambda>s. P s \<and> \<not>bval b s"])
  apply (rule assms(3); simp)
  apply (rule basic_while_rule)
  apply (rule conseq_pre_rule)
  apply (rule assms(1))
  apply (rule assms(2); auto)
  done

(* Automatic proof *)
lemma 
  assumes "\<Turnstile> {R} c {P}"
  assumes "\<And>s. \<lbrakk>P s; bval b s\<rbrakk> \<Longrightarrow> R s"
  assumes "\<And>s. \<lbrakk>P s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q s"
  shows "\<Turnstile> {P} WHILE b DO c {Q}"
  using conseq_pre_rule conseq_post_rule basic_while_rule
  by (smt assms)

end
