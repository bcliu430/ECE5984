theory Homework5_2
imports Main
begin

  (*
    ISSUED: Wednesday, October 18
    DUE: Wednesday, October 25, 11:59pm
    POINTS: 5
  *)


  (*
    In a directed graph, a path from node q to node v is the list of nodes 
    visited on the way from q to v, including the first node, and excluding 
    the last node.
    
    Inductively, we can characterize paths as follows:
  *)
  inductive path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
    "path E q [] q"
  | "\<lbrakk> E p q; path E q w r \<rbrakk> \<Longrightarrow> path E p (p#w) r"

  (*
    Functionally, we have the following characterization:
  *)
  lemma path_Nil_conv: "path E p [] q \<longleftrightarrow> q=p"
    by (auto elim: path.cases intro: path.intros)

  lemma path_Cons_conv: "path E p (x#xs) q \<longleftrightarrow> (x=p \<and> (\<exists>r. E p r \<and> path E r xs q))"
    by (auto elim: path.cases intro: path.intros)
    
  (* Prove the equivalence rule for appending two paths.
    Hint: Induction on w1, use the path_Nil_conv and path_Cons_conv 
      lemmas as simp-rules. Proof should be straightforward, probably no Isar required.
  *)  
  lemma path_append_conv: "path E p (w1@w2) q \<longleftrightarrow> (\<exists>r. path E p w1 r \<and> path E r w2 q)"
    sorry
  
  (*
    A path is called simple, if it visits each node at most once 
    (except for circular path, that, of course, visit their common 
      start and end node twice)
  
    For our path definition, a path is simple if and only if it contains 
    no node twice (Isabelle constant: distinct). Recall, the end node is excluded.
    
    Show: If there is a path from p to q, then there is also a 
      simple path from p to q.

    Proof sketch (informal):
      Induction on the length of the path (rule: length_induct)
        Assume we have a path xs from p to q.
        IH: For all shorter path, we can find a simple path
        To show: There is a simple path from p to q
      
        If xs is already distinct, we are done.
        Otherwise, xs must have the form xs = xs1@[x]@xs2@[x]@xs3 (thm not_distinct_decomp)
        hence, we obtain nodes p1 p2 such that
          p -xs1\<rightarrow> x   x\<rightarrow>p1   p1 -xs2\<rightarrow> x   x\<rightarrow>p2   p2 -xs3\<rightarrow> q
        
        Here, p -xs\<rightarrow> q denotes a path, and p\<rightarrow>q a single edge.
          
        by "dropping" the loop, we obtain a path  p -xs1@[x]@xs3\<rightarrow> q
        this path is shorter than the original path, so by IH, we have a simple path from p to q. 
        QED.
        
    Prove the lemma formally. Most probably, you will need Isar!
  *)
  lemma 
    assumes "path E p xs q"
    shows "\<exists>ys. distinct ys \<and> path E p ys q"
    using assms
  proof (induction xs rule: length_induct)
    case (1 xs)
    
    (* These two lines just assign more readable names to the premises and the IH *)
    note PREMS="1.prems"
    note IH="1.IH"
    
    (* Now we use these names *)
    thm PREMS (* We may assume that we have a path*)
    thm IH    (* For shorter path, there exists distinct paths *)
    term ?case (* We have to show that there exists a distinct path *)
    
    show ?case sorry (* Fill in your proof here! *)
  qed
  
  
end
