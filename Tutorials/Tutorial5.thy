theory Tutorial5
imports IMPArrayHoare "~~/src/HOL/Library/Multiset"
begin

context Imp_Array_Examples begin

section \<open>New Features\<close>

subsection \<open>Logical Variables\<close>
text \<open>
  Logical variables are included in Hoare-Triple
    \<open>(\<Turnstile> {P} c {Q}) = (\<forall>s t z. P z s \<and> (c, s) \<Rightarrow> t \<longrightarrow> Q z t)\<close>
    
    \<^item> Are the same in pre and post condition    
    \<^item> Used to carry over information
\<close>

text \<open>Examples\<close>

text \<open>Result in terms of previous variables\<close>
lemma "\<Turnstile>\<^sub>t {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0} x::=$x*\<acute>5 {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0*5}"
  by vcg
  
text \<open>Use tuples for multiple logical variables\<close>  
lemma "\<Turnstile>\<^sub>t {\<lambda>(x\<^sub>0,y\<^sub>0). vars x y in x=x\<^sub>0 \<and> y=y\<^sub>0} x::=$x*$y {\<lambda>(x\<^sub>0,y\<^sub>0). vars x in x=x\<^sub>0*y\<^sub>0}"
  by vcg

text \<open>Use dummy argument for no logical variables\<close>
lemma "\<Turnstile>\<^sub>t {\<lambda>_. vars x in x\<noteq>0} x ::= $x div $x {\<lambda>_. vars x in x=1}"
  by vcg
  
text \<open>Logical variables must be the same on both sides!\<close>  
lemma "\<Turnstile>\<^sub>t {\<lambda>(x\<^sub>0,y\<^sub>0). vars x y in x=x\<^sub>0 \<and> y=y\<^sub>0} x::=$x*$y {\<lambda>(x\<^sub>0). vars x in x=x\<^sub>0*y\<^sub>0}"
  oops (** type error! *)
  
text \<open>
  \<^item> Hoare-Rules do not significantly change due to introduction of logical variables.
  \<^item> But while-rule for total correctness becomes simpler
    \<^item> Uses logical variable to ensure decreasing states
    \<^item> Added to logical variables only for one precondition
  
\<close>
lemma 
  assumes "wf R"
  assumes "\<Turnstile>\<^sub>t {Ph} c {\<lambda>(z,s\<^sub>0) s. P z s \<and> (s, s\<^sub>0) \<in> R}"
  assumes "\<And>z s. \<lbrakk>P z s; bval b s\<rbrakk> \<Longrightarrow> Ph (z,s) s"
  assumes "\<And>z s. \<lbrakk>P z s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q z s"
  shows "\<Turnstile>\<^sub>t {P} WHILE b DO c {Q}"
  using assms while_trule by blast


subsection \<open>Modified Specification\<close>  
  
text \<open>
  Logical variables can be used to express which variables are not modified
  by a program.
  
    \<open>\<Turnstile>\<^sub>t {\<lambda>s\<^sub>0 s. P s \<and> s\<^sub>0=s } c {\<lambda>s\<^sub>0 t. Q t \<and> s\<^sub>0 = t on X}\<close>
    
    \<^item> Store previous state in logical variable, and specify unmodified 
      variables in postcondition.
    \<^item> @{term "s = t on X"}: States \<open>s\<close> and \<open>t\<close> equal on variables in set \<open>X\<close>
\<close>

text \<open>
  \<^item> More convenient to specify \<^emph>\<open>modified\<close> variables (it's only finitely many!)
  \<^item> Annotate them to Hoare-triples
  \<^item> Annotation is approximation: May contain more variables than actually modified, but never less!
\<close>

lemma "\<Turnstile>\<^sub>t {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0} x::=$x*\<acute>5 {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0*5} mod {''x''}"
  by vcg

(* Too many variables are OK *)  
lemma "\<Turnstile>\<^sub>t {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0} x::=$x*\<acute>5 {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0*5} mod {''x'',''y'',''z''}"
  by vcg
  
(* Too few are not! *)  
lemma "\<Turnstile>\<^sub>t {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0} CLR y;; x::=$x*\<acute>5 {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0*5} mod {''x''}"
  apply vcg
  (* Typical error message if modified variable annotation misses something *)
  oops

subsubsection \<open>Syntactic Approximation\<close>  
text \<open>
  \<^item> Indeed, by default a syntactic approximation will be used by VCG
  \<^item> Just take all variables occurring on LHS of assignments or are cleared
  
    @{term_type "lhs_vars :: com \<Rightarrow> vname set"}
    
  \<^item> The VCG uses the following lemma:
\<close>
lemma 
  assumes "lhs_vars c \<subseteq> X"
  assumes "\<Turnstile>\<^sub>t {P} c {Q}"
  shows "\<Turnstile>\<^sub>t {P} c {Q} mod X"
  using assms hoaret_modI by blast
  
(* x = 2^x\<^sub>0   *)    
lemma "\<Turnstile>\<^sub>t {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0 \<and> 0\<le>x} power2_prog {\<lambda>x\<^sub>0. vars x in x=2^nat x\<^sub>0} mod {''x''}"    
  oops  
    
subsection \<open>Framing\<close>

text \<open>
  \<^item> We have proven a nice specification of a complex program
\<close>
definition "mult5_prog \<equiv> x::=$x*\<acute>5"

lemma mult5_correct: "\<Turnstile>\<^sub>t {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0} mult5_prog {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0*5} mod {''x''}"
  unfolding mult5_prog_def
  by vcg


(* Declare lhs-vars for mult5_prog! *)
lemma [simp]: "lhs_vars mult5_prog = {''x''}" by (auto simp: mult5_prog_def)
  
  
text \<open>  
  \<^item> Now we want to use it as a subroutine in another program
\<close>

definition "mult25_prog \<equiv> mult5_prog;; mult5_prog"

lemma "\<Turnstile>\<^sub>t {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0} mult25_prog {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0*25} mod {''x''}"
  unfolding mult25_prog_def
  apply vcg 
  using mult5_correct
  oops

text \<open>
  \<^item> Problem: Specification not suited for VCG: It must work for all postconditions!

  \<^item> Solution: Frame rule (@{thm frame_rule}, @{thm frame_trule})
    \<open>   \<Turnstile> {P} c {Q} 
    \<Longrightarrow> \<Turnstile> {\<lambda>z s. \<exists>z'. P z' s \<and> (\<forall>t. Q z' t \<longrightarrow> R z t)} c {R}\<close>  
  
    Intuition:
      To ensure \<open>R\<close> after executing \<open>c\<close>, the precondition must ensure
        \<^item> P, (precondition to execute c)
        \<^item> R in the state \<open>t\<close> after executing c. 
          The only thing we know about \<open>t\<close> is that it will satisfy \<open>Q\<close>
    
      Moreover, we allow different sets of logical variables for 
        specification and program to be proved (\<open>z\<close> vs. \<open>z'\<close>)
\<close>

text \<open>
  \<^item> We also instantiate the frame rule for specifications with 
    modifies-annotations
    
    \<open>
        \<Turnstile> {P} c {Q} mod X 
    \<Longrightarrow> \<Turnstile> {\<lambda>z s. \<exists>z'. P z' s \<and> (\<forall>t. Q z' t \<and> s = t on - X \<longrightarrow> R z t)} c {R}\<close>
  
    \<^item> Here, we additionally know that the new state \<open>t\<close> is equal to the 
      start state \<open>s\<close> on all unmodified variables

  \<^item> These rules are integrated with the VCG, just declare the specification as 
    @{attribute vcg_rules}
      
\<close>

declare mult5_correct[vcg_rules]

lemma "\<Turnstile>\<^sub>t {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0} mult25_prog {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0*25} mod {''x''}"
  unfolding mult25_prog_def
  by vcg

(* Common error: Forgetting to CLR variable. *)    
    
lemma "\<Turnstile>\<^sub>t {\<lambda>x\<^sub>0. vars x y z in x=x\<^sub>0} (*CLR r;;*) r::=$x {\<lambda>x\<^sub>0. vars r x y z in r=x\<^sub>0} mod {''r''}"
  apply vcg oops

  

section \<open>Case Study: Minsort\<close>  
  
subsection \<open>Extracting a Range of an Array to a List\<close>  
function (sequential) lran :: "(int \<Rightarrow> val) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> val list" where
  "lran a l h = (if l<h then a l # lran a (l+1) h else [])"
  by pat_completeness auto
termination 
  by (relation "measure (\<lambda>(_,l,h). nat (h-l))") auto
  
declare lran.simps[simp del]  
  
text \<open>
  \<open>lran a l h\<close> is the list \<open>[a\<^sub>l,a\<^sub>l\<^sub>+\<^sub>1,...,a\<^sub>h\<^sub>-\<^sub>1]\<close>
\<close>

subsubsection \<open>Auxiliary Lemmas\<close>

lemma lran_empty[simp]: 
  "lran a l l = []"
  "lran a l h = [] \<longleftrightarrow> h\<le>l"
  by (rewrite lran.simps; auto)+

lemma lran_bwd_simp: "lran a l h = (if l<h then lran a l (h-1)@[a (h-1)] else [])"
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  apply (rewrite in "_ = \<hole>" lran.simps)
  by (auto simp: less_le)
    
    
lemma lran_append1[simp]: "l\<le>h \<Longrightarrow> lran a l (h + 1) = lran a l h @ [a h]"
  by (rewrite in "\<hole> = _" lran_bwd_simp) auto

lemma lran_prepend1[simp]: "l\<le>h \<Longrightarrow> lran a (l-1) h = a(l-1) # lran a l h"
  by (rewrite in "\<hole> = _" lran.simps) auto
    
lemma lran_tail[simp]: "lran a (l+1) h = tl (lran a l h)"
  apply (rewrite in "_ = \<hole>" lran.simps)
  apply auto
  done
    
lemma lran_butlast[simp]: "lran a l (h-1) = butlast (lran a l h)"
  apply (rewrite in "_ = \<hole>" lran_bwd_simp)
  apply auto
  done
  

lemma lran_upd_outside[simp]:
  "i<l \<Longrightarrow> lran (a(i:=x)) l h = lran a l h"
  "h\<le>i \<Longrightarrow> lran (a(i:=x)) l h = lran a l h"
  subgoal
    apply (induction a l h rule: lran.induct)
    apply (rewrite in "\<hole> = _" lran.simps)
    apply (rewrite in "_ = \<hole>" lran.simps)
    by (auto)
  subgoal
    apply (induction a l h rule: lran.induct)
    apply (rewrite in "\<hole> = _" lran.simps)
    apply (rewrite in "_ = \<hole>" lran.simps)
    by (auto)
  done  

lemma lran_eq_iff: "lran a l h = lran a' l h \<longleftrightarrow> (\<forall>i. l\<le>i \<and> i<h \<longrightarrow> a i = a' i)"  
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  apply (rewrite in "_ = \<hole>" lran.simps)
  apply auto
  by (metis antisym_conv not_less zless_imp_add1_zle)
  
lemma set_lran[simp]: "set (lran a l h) = a`{l..<h}"  
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  apply auto
  by (metis atLeastLessThan_iff image_iff not_less not_less_iff_gr_or_eq zless_imp_add1_zle)

  
lemma atLeastLessThan_lower_incr: "l<h \<Longrightarrow> {l::int..<h} = insert l ({l+1..<h})" by auto
 
  
lemma mset_lran[simp]: "mset (lran a l h) = image_mset a (mset_set {l..<h})"
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  by (auto simp: atLeastLessThan_lower_incr)

subsubsection \<open>Find Minimum\<close>
  
text \<open>Find index of minimum element in \<open>a i, ..., a (h-1)\<close>, return in \<open>j\<close>\<close>
definition "find_min \<equiv> 
  CLR j;; CLR k;; CLR m;;
  j::=$i;; k::=$i+\<acute>1;; m::=a\<^bold>[$j\<^bold>];;
  WHILE $k<$h DO (
    (* m stores current minimum element, j stores its index *)
    IF a\<^bold>[$k\<^bold>] < $m THEN
      m ::= a\<^bold>[$k\<^bold>];;
      j::=$k
    ELSE SKIP;;
    k::=$k+\<acute>1
  )"
  
  
lemma [simp]: "lhs_vars find_min 
  = {''k'', ''j'', ''m''}"  
  unfolding find_min_def by auto
  
(* Augment the type signature as long as no type variables ('a,'b,...) occur 
  in the output of the definition command! *)  
definition find_min_invar :: "int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> _"
  where
  "find_min_invar i h a j k m \<equiv> 
      i\<le>j \<and> j<h \<and> i<k \<and> k\<le>h            (* Everything in range *)
    \<and> m = a j \<and> a j = Min (a`{i..<k})"  (* m stores minimum element, j its index *) 
  
lemma set_intv_singleton[simp]: "{i::int..<i + 1} = {i}" by auto

lemma set_intv_plus:
  fixes l :: int shows "l\<^sub>0\<le>l \<Longrightarrow> {l\<^sub>0..<l + 1} = insert l {l\<^sub>0..<l}"
  by auto
  
lemma fmi_vcs_aux1: "i\<^sub>0 < k \<Longrightarrow> \<forall>x\<in>{i\<^sub>0..<k}. a\<^sub>0 k < (a\<^sub>0::int\<Rightarrow>int) x \<Longrightarrow> a\<^sub>0 k = Min (a\<^sub>0 ` {i\<^sub>0..<k + 1})"  
  apply (rule Min_eqI[symmetric])
  apply (auto simp: Ball_def) 
  using eq_iff by fastforce
  
lemma fmi_vcs:
  "\<lbrakk>k < h; find_min_invar i h a j k m; a k < m\<rbrakk> \<Longrightarrow> find_min_invar i h a k (k + 1) (a k)"
  "\<lbrakk>k < h; find_min_invar i h a j k m; \<not> a k < m\<rbrakk> \<Longrightarrow> find_min_invar i h a j (k + 1) m"
  "\<lbrakk>\<not> k < h; find_min_invar i h a j k m\<rbrakk> \<Longrightarrow> i \<le> j \<and> j < h \<and> a j = Min (a ` {i..<h})"
  "i < h \<Longrightarrow> find_min_invar i h a i (i + 1) (a i)"
  unfolding find_min_invar_def
  apply (simp_all add: fmi_vcs_aux1)
  subgoal 
    apply (clarsimp simp add: set_intv_plus min_def not_less)
    apply (rule Min_eqI)
    apply auto 
    by (metis atLeastLessThan_iff eq_iff image_eqI)
  done  


lemma find_min_correct[vcg_rules]: "\<Turnstile>\<^sub>t
  {\<lambda>_. vars i h (a:imap) in i<h} 
    find_min 
  {\<lambda>_. vars i h (a:imap) j in i\<le>j \<and> j<h \<and> (a j = Min (a`{i..<h}))} 
  mod {''j'',''k'',''m''}"
  unfolding find_min_def
  apply (rewrite annot_tinvar[where 
    R="measure_exp ($h - $k)" and
    I="\<lambda>_. vars i h (a:imap) j k m in find_min_invar i h a j k m"
  ])
  apply vcg_all

  (* If the VCs make the simplifier loop, some more 'creative' techniques may help.
  
    using fmi_vcs by metis+
  
    Or, apply them one by one!
  *)
  using fmi_vcs(1) apply assumption
  using fmi_vcs(2) apply assumption
  using fmi_vcs(3) apply metis
  using fmi_vcs(3) apply metis
  using fmi_vcs(3) apply metis
  using fmi_vcs(4) apply metis
  done
  
  
  
text \<open>Sort the array \<open>a\<close> in between indices \<open>l\<close> and \<open>h\<close>.
  Idea: Find minimum element in remaining part array,
    swap to end of already sorted part.
    
    \<open>i\<close> points to first element of unsorted part.
\<close>  
definition "minsort \<equiv> 
  CLR i;;
  i::=$l;;
  WHILE $i<$h DO (
    find_min;;
  
    CLR t;;
    t ::= a\<^bold>[$i\<^bold>];;
    a\<^bold>[$i\<^bold>] ::= a\<^bold>[$j\<^bold>];;
    a\<^bold>[$j\<^bold>] ::= $t;;
    
    i::=$i+\<acute>1
  )"
  
  
definition "sorted_spec l l' \<equiv> mset l' = mset l \<and> sorted l'"
  
(* verify that all types are inferred as int, and no polymorphic ('a) types remain! *)
definition "I_minsort a\<^sub>0 l\<^sub>0 h\<^sub>0 a i \<equiv> 
    l\<^sub>0\<le>i \<and> i\<le>h\<^sub>0 
  \<and> mset (lran a\<^sub>0 l\<^sub>0 h\<^sub>0) = mset (lran a l\<^sub>0 h\<^sub>0)   (* Array contains original elements *)
  \<and> sorted (lran a l\<^sub>0 i)                        (* Sorted part is sorted *)
  \<and> (\<forall>k1\<in>{l\<^sub>0..<i}. \<forall>k2\<in>{i..<h\<^sub>0}. a k1 \<le> a k2)  (* Every element of unsorted part \<ge> sorted part *)
  "


lemma [simp]: "lhs_vars minsort = {''i'', ''a'', ''t'', ''k'', ''j'', ''m''}"
  unfolding minsort_def by auto


lemma atLeastThan_insert_lower: "l\<le>h \<Longrightarrow> {l-1..<h} = insert (l-1) {l::int..<h}" by auto
  
lemma image_mset_subst_outside: "x\<notin>#s \<Longrightarrow> image_mset (f(x:=y)) s = image_mset f s"
  by (induction s) auto

lemma image_mset_subst_in_range:
  assumes "i\<in>{l::int..<h}"  
  shows "image_mset (f(i:=x)) (mset_set {l..<h}) = image_mset f (mset_set {l..<h}) - {#f i#} + {#x#}"
proof -  
  from assms have "l<h" "l\<le>i" "i<h" by auto
  then show ?thesis
    apply (induction rule: int_less_induct)
    apply (auto simp: atLeastThan_insert_lower image_mset_subst_outside)
    apply (simp add: antisym_conv)
    done
qed    
  
  
  
lemma minsort_vcs:  
  "\<lbrakk>I_minsort z l ha aa ia; ia \<le> j; j < ha; aa j = Min (aa ` {ia..<ha})\<rbrakk>
       \<Longrightarrow> I_minsort z l ha (aa(ia := Min (aa ` {ia..<ha}), j := aa ia)) (ia + 1)"
  "\<lbrakk>\<not> i < h; I_minsort z l h a i\<rbrakk> \<Longrightarrow> sorted_spec (lran z l h) (lran a l h)"
  "l \<le> h \<Longrightarrow> I_minsort z l h z l"  
  subgoal
    unfolding I_minsort_def
    apply (auto simp: sorted_append)
    apply (metis fun_upd_triv)
    apply (auto simp: image_mset_subst_in_range)
    done
  subgoal
    unfolding I_minsort_def sorted_spec_def
    by (auto)

  subgoal
    unfolding I_minsort_def
    by (auto)
  
  done
  
  
lemma minsort_correct: "\<Turnstile>\<^sub>t
  {\<lambda>a\<^sub>0. vars l h (a:imap) in l\<le>h \<and> a=a\<^sub>0}
    minsort
  {\<lambda>a\<^sub>0. vars l h (a:imap) in sorted_spec (lran a\<^sub>0 l h) (lran a l h) } 
    mod {''i'',''t'',''j'',''k'',''m'',''a''}"
  
  unfolding minsort_def
  apply (rewrite annot_tinvar[where 
    R = "measure_exp ($h - $i)" and
    I = "\<lambda>a\<^sub>0. vars l h (a:imap) i in I_minsort a\<^sub>0 l h a i"
    ])
  supply minsort_vcs[simp]  
  by vcg
  
end


end
