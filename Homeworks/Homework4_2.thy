theory Homework4_2
imports Main
begin

  (*
    ISSUED: Wednesday, October 11
    DUE: Wednesday, October 18, 11:59pm
    POINTS: 5
  *)

  (*
    In a directed graph, we have a path of length n from u to v,
    if we can go from u to v using exactly n edges. 

    Specify an inductive predicate pol E x n y, which is true if and only
    if there is a path of length n from x to y.
  *)
  
inductive pol :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" where
  empty: "pol E a 0 a"
  | step:"\<lbrakk>E a b; pol E b n c\<rbrakk> \<Longrightarrow> pol E a n c"
    (* Add inductive specification here! *)
     
  (* Show that two paths can be appended. Their length is the sum of the two lengths.
    Hint: Make sure the premises are in the right order,
      as rule induction will pick the first matching premise.
      If not, use rotate_tac.
  *)  
lemma pol_append: "\<lbrakk>pol E x k y; pol E y l z\<rbrakk> \<Longrightarrow> pol E x (k+l) z"
  apply (induction)
    
    sorry

  (*
    Write a recursive function that checks whether there is a path of length n.
    Hint: Recursion over n. Use an \<exists>-quantifier to obtain a next state.
  *)
      
  fun fpol :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
    where
    "fpol E a 0 b  \<longleftrightarrow> false"
  | "fpol E a (n#ns) b \<longleftrightarrow> (\<exists>q. E a q b \<and> fpol L b ns c)"
(* *)

  (* Show that the function is equivalent to the inductive version! 

    You may either show the two directions separately, as indicated in this template.
    Alternatively, you may derive recursive equations for pol, as done in LTS.thy.

    The only lemma that MUST be proved at the end is fpol_eq_pol!
  *)  
  lemma fpol_imp_pol: "fpol E x l y \<Longrightarrow> pol E x l y"
    sorry
      
  lemma pol_imp_fpol: "pol E x l y \<Longrightarrow> fpol E x l y"
    sorry
    
  lemma fpol_eq_pol: "fpol = pol" 
    sorry
      
  (* Using fpol, show that a path can be split *)    
  lemma fpol_split: "fpol E x (l1+l2) z \<Longrightarrow> (\<exists>y. fpol E x l1 y \<and> fpol E y l2 z)"    
    sorry
      
  (* Combine the split and append lemma *)
  lemma pol_append_conv: "pol E x (l1+l2) z \<longleftrightarrow> (\<exists>y. pol E x l1 y \<and> pol E y l2 z)"
    sorry

end
