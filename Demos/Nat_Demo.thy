theory Nat_Demo
imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

(* Automatic proof. This is what we will focus on first! *)    
lemma "add m 0 = m"
  apply(induction m)
  apply(auto)
  done


(* Completely manual proof. You do not need to understand 
  all the syntax details etc right now!     *)    
thm add.simps(1)
thm refl  

lemma "add m 0 = m"
  apply(induction m)
  (* Base case *)  
   apply (subst add.simps(1)) (* Rewrite with first equation of add *) 
   apply (rule refl) (* Use reflexivity: Syntactically equal terms are actually equal! *)
    
  (* Induction step *)  
  subgoal premises prems for m
    apply (subst add.simps(2)) (* Rewrite with second equation of add *) 
    thm prems  (* Diagnostic command to display induction hypothesis (assumption): *)
    apply (subst prems) (* Rewrite with I.H. *)
    apply (rule refl) (* Reflexivity again *)
    done
  done    

    

fun gs :: "nat \<Rightarrow> nat" where
  "gs 0 = 0"
| "gs (Suc n) = Suc n + gs n"  
    
lemma "gs n = n*(n+1) div 2"
  apply (induction n)
  apply auto
  done  
    
  
end
