chapter \<open>Auxiliary Lemma Library\<close>  
theory IPP_Lib
imports IMPlusPlus "~~/src/HOL/Library/Multiset"
begin

text \<open>This library contains auxiliary lemmas, which are useful for proving 
  various VCs.
  
  The locale declares some more simplification lemmas.
\<close>
  
locale Vcg_Aux_Lemmas  
  
section \<open>Conversion between Nat and Int\<close>  
lemmas (in Vcg_Aux_Lemmas) [simp] = nat_add_distrib

lemma int_minus_minus_eq: "(n\<^sub>0 - (n - 1)) = (n\<^sub>0 - (n::int)) + 1"
  by linarith

lemma nat_minus_minus_eq_Suc: 
  "0\<le>n \<and> n\<le>n\<^sub>0 \<Longrightarrow> nat (n\<^sub>0 - (n - 1)) = Suc (nat (n\<^sub>0-n))"
  -- \<open>Useful for count-down loop schemes\<close>
  by linarith

lemma int_plus_int_eq_int: "int a + int b = int (c) \<longleftrightarrow> a+b = c" by auto

lemmas (in Vcg_Aux_Lemmas) [simp] = 
  int_plus_int_eq_int nat_minus_minus_eq_Suc int_minus_minus_eq

section \<open>Interval Sets\<close>

lemma intvs_singleton[simp]: 
  "{i::int..<i + 1} = {i}" 
  "{i-1..<i::int} = {i-1}" 
  by auto

lemma intvs_incr_h:
  "l\<le>h \<Longrightarrow> {l::int..<h + 1} = insert h {l..<h}"
  by auto

lemma intvs_decr_h:
  "{l::int..<h - 1} = {l..<h} - {h-1}"
  by auto
  
lemma intvs_incr_l:
  "{l+1..<h::int} = {l..<h} - {l}"
  by auto

lemma intvs_decr_l:
  "l\<le>h \<Longrightarrow> {l-1..<h::int} = insert (l-1) {l..<h}"
  by auto
  
lemmas intvs_incdec = intvs_incr_h intvs_incr_l intvs_decr_h intvs_decr_l

lemma intvs_lower_incr: "l<h \<Longrightarrow> {l::int..<h} = insert l ({l+1..<h})" by auto
lemma intvs_upper_decr: "l<h \<Longrightarrow> {l::int..<h} = insert (h-1) ({l..<h-1})" by auto

section \<open>Induction on Intervals\<close>

function intv_fwd_induct_scheme :: "int \<Rightarrow> int \<Rightarrow> unit" where
  "intv_fwd_induct_scheme l h = (if l<h then intv_fwd_induct_scheme (l+1) h else ())"
  by pat_completeness auto
termination apply (relation "measure (\<lambda>(l,h). nat (h-l))") by auto 
lemmas intv_induct = intv_fwd_induct_scheme.induct[case_names incr]

function intv_bwd_induct_scheme :: "int \<Rightarrow> int \<Rightarrow> unit" where
  "intv_bwd_induct_scheme l h = (if l<h then intv_bwd_induct_scheme l (h-1) else ())"
  by pat_completeness auto
termination apply (relation "measure (\<lambda>(l,h). nat (h-l))") by auto 
lemmas intv_bwd_induct = intv_bwd_induct_scheme.induct[case_names decr]
  


section \<open>Multiset Lemmas\<close>

lemma image_mset_subst_outside: "x\<notin>#s \<Longrightarrow> image_mset (f(x:=y)) s = image_mset f s"
  by (induction s) auto
  
lemma image_mset_set_subst_inside:
  assumes "finite S"
  assumes "i\<in>S"
  shows "image_mset (f(i:=x)) (mset_set S) = image_mset f (mset_set S) + {#x#} - {#f i#} "
  using assms  
  by (induction rule: finite_induct) (auto simp: image_mset_subst_outside)

section \<open>Multiset of Ranges in Arrays\<close>  
definition mset_ran :: "(int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a multiset"
  where "mset_ran a l h \<equiv> image_mset a (mset_set {l..<h})"

lemma mset_ran_by_sum: "mset_ran a l h = (\<Sum>i=l..<h. {#a i#})"
proof (induction l h rule: intv_induct)
  case (incr l h)
  then show ?case 
    unfolding mset_ran_def
    by (cases "l<h") (auto simp: intvs_lower_incr)
    
qed

lemma mset_ran_mem[simp, intro]: "i\<in>{l..<h} \<Longrightarrow> a i \<in># mset_ran a l h"
  by (auto simp: mset_ran_def)

lemma mset_ran_empty[simp]: 
  "mset_ran a l l = {#}"  
  by (auto simp: mset_ran_def)
  
lemma mset_ran_empty_iff[simp]: 
  "mset_ran a l h = {#} \<longleftrightarrow> h\<le>l"
  by (auto simp: mset_ran_def mset_set_empty_iff)

lemma mset_ran_subst_outside: "i\<notin>{l..<h} \<Longrightarrow> mset_ran (a(i:=x)) l h = mset_ran a l h"  
  unfolding mset_ran_def by (auto simp: image_mset_subst_outside)

lemma mset_ran_subst_inside: "i\<in>{l..<h} \<Longrightarrow> mset_ran (a(i:=x)) l h = mset_ran a l h + {#x#} - {#a i#}"  
  unfolding mset_ran_def by (auto simp: image_mset_set_subst_inside)
  
lemma mset_ran_combine: "\<lbrakk>i\<le>j; j\<le>k\<rbrakk> \<Longrightarrow> mset_ran a i j + mset_ran a j k = mset_ran a i k"
  by (auto simp: mset_ran_by_sum sum.union_disjoint[symmetric] ivl_disj_un)
  
lemma mset_ran_cong:  
  "a = b on {l..<h} \<Longrightarrow> mset_ran a l h = mset_ran b l h"
  by (auto simp: mset_ran_by_sum eq_on_def)
  
lemma extend_range:
  assumes BOUNDS: "l\<le>h" "h\<le>h'"
  assumes EQ1: "mset_ran a l h = mset_ran a\<^sub>0 l h"
  assumes EQ2: "a = a\<^sub>0 on {h..<h'}"
  shows "mset_ran a l h' = mset_ran a\<^sub>0 l h'"
  using EQ1 mset_ran_cong[OF EQ2] 
    mset_ran_combine[OF BOUNDS, of a]
    mset_ran_combine[OF BOUNDS, of a\<^sub>0]
    by simp
  
  
  
  

end
