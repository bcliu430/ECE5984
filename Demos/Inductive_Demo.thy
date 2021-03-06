theory Inductive_Demo
imports Main
begin

subsection{*Inductive definition of the even numbers*}

  
  
  
inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

thm ev0 evSS
thm ev.intros

text{* Using the introduction rules: *}
lemma "ev (Suc(Suc(Suc(Suc 0))))"
oops

thm evSS[OF evSS[OF ev0]]

text{* A recursive definition of evenness: *}
fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text{*A simple example of rule induction: *}
lemma "ev n \<Longrightarrow> evn n"
  apply(induction rule: ev.induct)
    by auto


text{* An induction on the computation of evn: *}
lemma "evn n \<Longrightarrow> ev n"
  apply(induction n rule: evn.induct)
    apply (simp add: ev0)
   apply simp
  apply (rule evSS)
  apply simp
    done

lemma "evn n \<Longrightarrow> ev n"
  apply(induction n rule: evn.induct)
  apply (auto intro: ev.intros)  
  done
      
      
      
text{* No problem with termination because the premises are always smaller
than the conclusion: *}
declare ev.intros[simp,intro]

text{* A shorter proof: *}
lemma "evn n \<Longrightarrow> ev n"
apply(induction n rule: evn.induct)
apply(simp_all)
done

text{* The power of arith: *}
lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k"
  apply(induction rule: ev.induct)
    apply auto try0
  by presburger
    


subsection{*Inductive definition of the reflexive transitive closure *}

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
apply(assumption)
apply (blast intro: step)
done

(* The last definition defines star by prepending a new element in every step.
  We could also have defined it by appending a new element:
*)  

inductive
  star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl':  "star' r x x" |
step':  "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star'_trans:
  "star' r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z" 
apply (rotate_tac)  (* Note: Rule induction applies to first assumption! 
  However, we need to induction on the derivation of star' r y z! 
  With Isar, we will be able to write this more concisely.
*)
apply(induction rule: star'.induct)
apply(assumption)
apply (blast intro: step')
done

(* To prove equality of star and star', it's a good idea to prove both directions \<Longrightarrow> and \<Longleftarrow> separately: *)  

lemma star_imp_star': "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
   apply (rule refl')
  thm star'_trans[OF step'[OF refl']] (* Let's assemble a suitable theorem to solve the second subgoal *)
  apply (rule star'_trans[OF step'[OF refl']])  
  apply (assumption)  
  apply (assumption)  
  done  

(* Of course, we can summarize the whole proof into a single auto application *)    
lemma "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
  apply (auto intro: refl' star'_trans[OF step'[OF refl']])
  done  
    
(* The other direction *)    
lemma star'_imp_star: "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
  thm star_trans[OF _ step[OF _ refl]]
  by (auto intro: refl star_trans[OF _ step[OF _ refl]])

(* The equality lemma *)    
lemma star'_eq_star: "star' r x y = star r x y"
  by (auto intro: star_imp_star' star'_imp_star)
    
(* We can also omit the arguments *)  
thm ext    
lemma "star' = star"
  apply (rule ext)
  apply (rule ext)
  apply (rule ext)
  by (rule star'_eq_star)
    
thm ext (* Two functions are equal if they are equal for any argument *)   
    
lemma "star' = star"
  apply (intro ext) (* Apply given rules as often as possible *)
  by (rule star'_eq_star)
  
  
end
