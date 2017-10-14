theory Tutorial3
imports Main
begin

  (*
    A labeled transition system (LTS) is a directed graph where the edges 
    are annotated with labels. 

    A word from node q to node v is a list of labels, corresponding
    to the edges on a path from q to v.

    For example, the well known concept of finite automata, is usually 
    represented as an LTS with an initial state and a set of final states.
  *)
  
  type_synonym ('q,'a) lts = "'q \<Rightarrow> 'a \<Rightarrow> 'q \<Rightarrow> bool"
  
    
  inductive word :: "('q,'a) lts \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" where
    empty: "word L q [] q"
  | step: "\<lbrakk> L q a r; word L r as s \<rbrakk> \<Longrightarrow> word L q (a#as) s"  
  
  lemma word_append: "\<lbrakk>word L p as q; word L q bs r\<rbrakk> \<Longrightarrow> word L p (as@bs) r"
    apply (induction rule: word.induct)
     apply simp
    apply simp
    apply (rule step) 
     apply assumption
      by assumption
      
  lemma "\<lbrakk>word L p as q; word L q bs r\<rbrakk> \<Longrightarrow> word L p (as@bs) r"
    apply (induction rule: word.induct)
    apply (auto intro: word.intros)
    done  

  lemma word_split: "word L p (as@bs) r \<Longrightarrow> (\<exists>q. word L p as q \<and> word L q bs r)"
    (* Try to instantiate induction rule *)
    apply (induction L p "as@bs" r arbitrary: as rule: word.induct)
     apply (auto intro: word.intros simp: Cons_eq_append_conv) 
    by (fastforce intro: word.intros)  
      
      
  (* Sometimes, induction over a different structure, and case analysis, may be simpler: 

    To add case-distinctions over an inductive predicate to the rules that auto/blast/force/...
    try automatically, use the elim: modifier. The rule is called <name>.cases
  *)
  thm word.cases
  lemma "word L p (as@bs) r \<Longrightarrow> (\<exists>q. word L p as q \<and> word L q bs r)"
    apply (induction as arbitrary: p)
     apply (auto intro: empty) 
     thm word.cases 
     apply (erule word.cases)
      apply simp
     apply (force intro: word.intros )
     done  

       
  (* Combining both lemmas *)    
  lemma word_append_conv: "word L p (as@bs) r \<longleftrightarrow> (\<exists>q. word L p as q \<and> word L q bs r)"
    by (auto simp: word_append word_split)

      
  (* Sometimes, we can also write an inductive predicate as a function.
    For example, the empty and append equations hint at function equations
    that recurse over the list!
  *)
      
  thm empty word_append_conv
    
  (* We can refine them a bit *)  
  (* In the proofs, we only need to do a case distinction over word ... 
    no induction is required.

  *)
  lemma word_Nil_conv: "word L p [] q \<longleftrightarrow> p=q"
    by (auto intro: empty elim: word.cases)
    
  lemma word_Cons_conv: "word L p (a#bs) r \<longleftrightarrow> (\<exists>q. L p a q \<and> word L q bs r)"
    apply auto
     apply (erule word.cases)  
      apply simp
     apply auto
    apply (auto intro: intro: word.intros)
    done  
      
  lemma "word L p (a#bs) r \<longleftrightarrow> (\<exists>q. L p a q \<and> word L q bs r)"
    by (force intro: word.intros elim: word.cases)
    
  (* Once we have proven the above rules, we can directly encode them as a function *)
  fun fword :: "('q,'a) lts \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" 
    where 
    "fword L p [] q \<longleftrightarrow> p=q"
  | "fword L p (a#bs) r \<longleftrightarrow> (\<exists>q. L p a q \<and> fword L q bs r)"
      

  (* Proving equality to the inductive predicate is then straightforward,
    by induction on the function / structural induction *)
lemma "fword L p w q \<longleftrightarrow> word L p w q"
  apply (induction L p w q rule: fword.induct)
   apply (auto simp: word_Nil_conv word_Cons_conv)
   done 
    
lemma "fword L p w q \<longleftrightarrow> word L p w q"
  apply (induction w arbitrary: p)
   apply (auto simp: word_Nil_conv word_Cons_conv)
   done 

end
