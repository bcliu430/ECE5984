theory Homework4_2sol
imports Main
begin
  (* Path with length *)    

  (*
    In a directed graph, we have a path of length n from u to v,
    if we can go from u to v using exactly n edges. 

    Specify an inductive predicate pol E x n y, which is true if and only
    if there is a path of length n from x to y.
  *)
  
  inductive pol :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" 
  (*<*)  
    where
    refl: "pol E x 0 x"
  | trans: "\<lbrakk> E x y; pol E y l z \<rbrakk> \<Longrightarrow> pol E x (Suc l) z"  
  (*>*)  
     
  (* Show that two paths can be appended. Their length is the sum of the two lengths.
    Hint: Make sure the premises are in the right order,
      as rule induction will pick the first matching premise.
      If not, use rotate_tac.
  *)  
  lemma pol_append: "\<lbrakk>pol E x k y; pol E y l z\<rbrakk> \<Longrightarrow> pol E x (k+l) z"
  (*<*)  
    apply (induction rule: pol.induct)
    by (auto intro: pol.intros)
  (*>*)  

  (**
    Note: In general, you should write the conclusions of intro-rules
    such that they do not simplify any more wrt the default simpset ...

    Try, e.g.:
  *)
  
  inductive pol' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" 
  (*<*)  
    where
    refl': "pol' E x 0 x"
  | trans': "\<lbrakk> E x y; pol' E y l z \<rbrakk> \<Longrightarrow> pol' E x (l+1) z"  
  (*>*)  
     
  lemma pol'_append: "\<lbrakk>pol' E x k y; pol' E y l z\<rbrakk> \<Longrightarrow> pol' E x (k+l) z"
    apply (induction rule: pol'.induct)
    apply (auto intro: pol.intros) (** Does not solve the goal \<dots> in this case, sledgehammer helps you out, however *)
    (** The reason here is, that the conclusion of rule trans' (_+1)  
      does not syntactically match (Suc (_+_)).
      
      The Suc comes in, as the simplifier will rewrite any _+1 on nat to Suc _.
      
      Thus, the best way to get around this, is to modify your trans'-rule and let it use Suc, too.
    *)    
    using trans' by fastforce
  

  (* You can do a quick check of your rules \<dots> *)  
  thm trans' trans'[simplified] -- \<open>Observe the changes introduced by the simplifier\<close>
  
  thm trans trans[simplified] -- \<open>No changes here ... \<close>
    
  (* Note that this check does not cover all cases: 
    If your rules fail this check, they are unlikely to match any simplified goal
    But: If your rules pass the check, they may still fail to apply the goal.
      Consider, e.g. the introduction rule: \<dots> \<Longrightarrow> P (a+b)
        and the goal: P (a+0)
      This will simplify to P a, and your intro-rule does not match any more.
  *)
  
  (* Usually, you can solve these problems also on Isar-level, 
    e.g., by forward reasoning: 
  *)
  lemma "\<lbrakk>pol' E x k y; pol' E y l z\<rbrakk> \<Longrightarrow> pol' E x (k+l) z"
  proof (induction rule: pol'.induct)
    case (refl' E x)
    then show ?case by (simp)
  next
    case (trans' E x y k zz)
    hence "pol' E y (k + l) z" by blast
    from pol'.trans'[OF \<open>E x y\<close> this] show ?case by simp
  qed
  
  
  
  
  
  (*
    Write a recursive function that checks whether there is a path of length n.
    Hint: Recursion over n! Use an \<exists>-quantifier to obtain a next state.
  *)
      
  fun fpol :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
    (*<*)
    where
    "fpol E x 0 y \<longleftrightarrow> x=y"
  | "fpol E x (Suc n) z \<longleftrightarrow> (\<exists>y. E x y \<and> fpol E y n z)"  
    (*>*)

  (* Show that the function is equivalent to the inductive version! *)  
  lemma fpol_imp_pol: "fpol E x l y \<Longrightarrow> pol E x l y"
    (*<*)
    apply (induction l arbitrary: x)
    apply (auto intro: pol.intros)  
    done
    (*>*)
      
  lemma pol_imp_fpol: "pol E x l y \<Longrightarrow> fpol E x l y"
    (*<*)
    apply (induction rule: pol.induct)
    apply auto
    done  
    (*>*)
    
  lemma fpol_eq_pol: "fpol = pol" 
    (*<*)
    apply (intro ext)
    using fpol_imp_pol pol_imp_fpol by auto
    (*>*)  
      
  (* Using fpol, show that a path can be split *)    
      
  lemma fpol_split: "fpol E x (l1+l2) z \<Longrightarrow> (\<exists>y. fpol E x l1 y \<and> fpol E y l2 z)"    
    (*<*)
    by (induction l1 arbitrary: x) force+  
    (*>*)  
      
  (* Combine the split and append lemma *)
  lemma pol_append_conv: "pol E x (l1+l2) z \<longleftrightarrow> (\<exists>y. pol E x l1 y \<and> pol E y l2 z)"
    (*<*)
    using pol_append fpol_split by (auto simp: fpol_eq_pol)
    (*>*)  
      

end
