theory Homework5_1sol
imports Main
begin

  (*
    ISSUED: Wednesday, October 18
    DUE: Wednesday, October 25, 11:59pm
    POINTS: 5
  *)

  (*
    Recall the LTS formalization from the tutorial. 
    I copied the important parts here:
  *)
  
section \<open>Parts of LTS from Tutorial\<close>  
type_synonym ('q,'a) lts = "'q \<Rightarrow> 'a \<Rightarrow> 'q \<Rightarrow> bool"


inductive word :: "('q,'a) lts \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" 
  where
    empty: "word L q [] q"
  | cons: "\<lbrakk> L p a q; word L q as r \<rbrakk> \<Longrightarrow> word L p (a#as) r"

lemma word_Nil_conv: "word L p [] q \<longleftrightarrow> p=q"
  by (auto elim: word.cases intro: word.intros)
  
lemma word_Cons_conv: "word L p (a#bs) r \<longleftrightarrow> (\<exists>q. L p a q \<and> word L q bs r)"
  by (auto elim: word.cases intro: word.intros)
  
lemma word_append_conv: "word L p (as@bs) r \<longleftrightarrow> (\<exists>q. word L p as q \<and> word L q bs r)"
  (* Slightly changed proof compared to tutorial *)
  by (induction as arbitrary: p) (auto simp: word_Nil_conv word_Cons_conv)

section \<open>Product Construction\<close>  
(* Here starts the homework assignment *)  
  
(*
  For a labeled transition system, we define the language
  from state p to state q as the set of all words from p to q. 
*)
definition "lang L p q = {w. word L p w q}"  


(*
  The product "prod L1 L2" of two labeled transition systems L1 :: ('p,'a) lts 
  and L2 :: ('q,'a) lts is a labeled transition system over states of
  type 'p\<times>'q. We define (prod L1 L2) (p1,q1) a (p2,q2) iff 
  L1 p1 a p2 and L2 q1 a q2.
*)
definition L_prod :: "('p,'a) lts \<Rightarrow> ('q,'a) lts \<Rightarrow> ('p\<times>'q,'a) lts" where
  "L_prod L1 L2 \<equiv> \<lambda>(p1,p2) l (q1,q2). L1 p1 l q1 \<and> L2 p2 l q2"

(*
  Intuitively, a transition of the product corresponds to a transition 
  of both components, with the same label.
*)  

(*
  Show that the language of the product LTS corresponds to the 
  intersection of the languages of the component LTSs.
  
  Proof sketch:
    assume we have a word w in the product language.
    hence, we have "word (L_prod L1 L2) (p1, p2) w (q1, q2)"
    by induction on w, we get word L1 p1 w q1 and word L2 p2 w q2
    from which, by definition of lang, we get the proposition.
  
    the proof of the other direction is symmetric.
    
  Use an Isar proof! Note: There is no notion of "symmetric" in Isar, so 
    you will have to actually prove both directions.
    
  Hint: In the induction proofs, use the structural equations  
     word_Cons_conv word_Nil_conv as simp rules, rather than 
     the word.intros and word.cases rules. 
     Don't forget to generalize over some variables!
    
*)

  lemma "lang (L_prod L1 L2) (p1,p2) (q1,q2) = (lang L1 p1 q1 \<inter> lang L2 p2 q2)"
  proof (intro equalityI subsetI)  
    fix w
    assume "w \<in> lang (L_prod L1 L2) (p1, p2) (q1, q2)" 
    hence "word (L_prod L1 L2) (p1, p2) w (q1, q2)" by (auto simp: lang_def)
    hence "word L1 p1 w q1 \<and> word L2 p2 w q2"
      by (induction w arbitrary: p1 p2) (auto simp: word_Cons_conv word_Nil_conv L_prod_def)
    thus "w \<in> lang L1 p1 q1 \<inter> lang L2 p2 q2"
      by (auto simp: lang_def)
  next
    fix w
    assume "w \<in> lang L1 p1 q1 \<inter> lang L2 p2 q2"
    hence "word L1 p1 w q1" "word L2 p2 w q2" by (auto simp: lang_def)
    hence "word (L_prod L1 L2) (p1, p2) w (q1, q2)"
      by (induction w arbitrary: p1 p2) (auto simp: word_Cons_conv word_Nil_conv L_prod_def)
    thus "w \<in> lang (L_prod L1 L2) (p1, p2) (q1, q2)" by (auto simp: lang_def) 
  qed

end
