theory Palindrome
imports Main
begin
(*
  Palindromes are words that read the same backward as forward.
  
  Lemma: Exactly the palindromes can be constructed by the following rules
*)

inductive pal :: "'a list \<Rightarrow> bool" where
  empty: "pal []"
| single: "pal [x]"  
| append: "pal xs \<Longrightarrow> pal (x#xs@[x])"  

(* One direction of the proof is easy. *)
lemma pal_sound: "pal xs \<Longrightarrow> rev xs = xs" by (induction rule: pal.induct) auto

(* Let's focus on the other direction *)
lemma pal_complete:
  assumes "rev xs = xs" 
  shows "pal xs"
  oops
(*
  Proof sketch
  
    induction on length of xs
      PREM: rev xs = xs
      IH: for all ys shorter than xs and with rev ys = ys, we have pal ys
      To show: pal xs

      If xs is empty or the singleton list, the goal follows by empty/single rule
      So assume xs = x#zs@[y]. 
      From PREM, we get that y=x and rev zs = zs.
      Moreover, zs is shorter than xs
      hence, by IH, we have pal zs
      and, by pal.append, we get pal (x#zs@[x])
      with the equalities form above, we have xs = x#zs@[x], and thus pal xs. 
      QED
      

*)



lemma pal_complete:
  assumes "rev xs = xs" 
  shows "pal xs"
  using assms  
proof (induction xs rule: length_induct)
  case (1 xs)
  
  note IH="1.IH" note PREM="1.prems"
  
  show ?case proof (cases xs)
    case Nil
    then show ?thesis 
      by (simp add: pal.empty)
  next
    case (Cons x ys)
    then show ?thesis proof (cases ys rule: rev_cases)
      case Nil
      then show ?thesis
        using Cons by (simp add: pal.single)
    next
      case (snoc zs y)
      from PREM have "y=x" "rev zs = zs"
        by (auto simp: local.Cons snoc snoc_eq_iff_butlast)
        (* Simplifier loops, used sledgehammer to find the following proof *)
        (*apply (simp add: Cons snoc) 
        apply (unfold snoc) *)
        
      moreover have "length zs < length xs" by (simp add: Cons snoc)
      ultimately have "pal zs" using IH by blast
      hence "pal (x#zs@[x])" by (rule pal.append)
      then show ?thesis by (simp add: Cons snoc \<open>y=x\<close>)
    qed
  qed
qed

(* Same lemma, but adding simplifier setup *)

(* Adding a reasonable simplifier setup *)
lemmas [simp]  = pal.empty pal.single

lemma 
  assumes "rev xs = xs" 
  shows "pal xs"
  using assms  
proof (induction xs rule: length_induct)
  case (1 xs)
  
  note IH="1.IH" note PREM="1.prems"
  
  show ?case proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case [simp]: (Cons x ys) (* Adding local simp-lemma *)
    then show ?thesis proof (cases ys rule: rev_cases)
      case Nil
      then show ?thesis by (simp)
    next
      case [simp]: (snoc zs y)
      from PREM have [simp]: "y=x" and "rev zs = zs"  
        (* Names and attributes apply only to their part in "and" list, i.e.,
          the above declares \<open>y=x\<close> as simp lemma, but not \<open>rev zs = zs\<close> *)
        by (auto simp: snoc_eq_iff_butlast)
      moreover have "length zs < length xs" by simp
      ultimately have "pal zs" using IH by blast
      hence "pal (x#zs@[x])" by (rule pal.append)
      then show ?thesis by simp
    qed
  qed
qed

lemma pal_correct: "pal xs \<longleftrightarrow> rev xs = xs"
  using pal_sound pal_complete by auto


end
