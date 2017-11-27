theory Isar_Demo
imports Complex_Main
begin

section{* An introductory example *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

text{* A bit shorter: *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from 1 show "False" by blast
qed

subsection{* this, then, hence and thus *}

text{* Avoid labels, use this: *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

text{* then = from this *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  then have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then show "False" by blast
qed

text{* hence = then have, thus = then show *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  thus "False" by blast
qed


subsection{* Structured statements: fixes, assumes, shows *}

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -  --"no automatic proof step!"
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def)
  thus "False" by blast
qed


section{* Proof patterns *}

thm iffI

lemma "P \<longleftrightarrow> Q"
proof
  assume "P"
  show "Q" sorry
next
  assume "Q"
  show "P" sorry
qed

  
thm equalityI  
  
lemma "A = (B::'a set)"
proof
  show "A \<subseteq> B" sorry
next
  show "B \<subseteq> A" sorry
qed

thm subsetI
  
lemma "A \<subseteq> B"
proof
  fix a
  assume "a \<in> A"
  show "a \<in> B" sorry
qed

(* Sometimes, you want to combine equalityI and subsetI *)  
lemma "A = (B::'a set)"
proof (intro equalityI subsetI)
  fix x assume "x\<in>A" show "x\<in>B" sorry
next
  fix x assume "x\<in>B" show "x\<in>A" sorry
qed
  
lemma "{x. \<exists>y. x=y+y} = {x::nat. even x}"
proof (intro equalityI subsetI)
  fix x::nat assume "x\<in>{x. \<exists>y. x=y+y}" 
  hence "\<exists>y. x=y+y" by simp
  thus "x\<in>{x. even x}" by auto
next
  fix x::nat assume "x\<in>{x. even x}" thus "x\<in>{x. \<exists>y. x=y+y}" sorry
qed
  
  
lemma "A = (B::'a set)"
proof
  show "A \<subseteq> B" proof
    fix x assume "x \<in> A" show "x\<in>B" sorry
  qed      
next
  show "B \<subseteq> A" proof
    fix x assume "x \<in> B" show "x\<in>A" sorry
  qed      
qed


  
  
text{* Contradiction *}

lemma P 
proof (rule ccontr)
  assume "\<not>P"
  show "False" sorry
qed

text{* Case distinction *}

lemma "R"
proof cases
  assume "P"
  show "R" sorry
next
  assume "\<not> P"
  show "R" sorry
qed

  
lemma "R"
proof (cases "P::bool")
  assume "P"
  show "R" sorry
next
  assume "\<not> P"
  show "R" sorry
qed
  
  
lemma "R"
proof -
  have "P \<or> Q" sorry
  then show "R"
  proof
    assume "P"
    show "R" sorry
  next
    assume "Q"
    show "R" sorry
  qed
qed

text \<open>\<open>\<forall>\<close> introduction\<close>
  
lemma "\<forall>x. x < Suc x"
proof
  fix x
  show "x<Suc x" by simp
qed      

text \<open>\<open>\<exists>\<close> elimination\<close>  
  
lemma "\<exists>x. Suc x < 3"  
proof
  show "Suc 0 < 3" by simp
qed  
  
text{* obtain example *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed


text{* Interactive exercise: *}

lemma assumes A: "\<exists>x. \<forall>y. P x y" shows "\<forall>y. \<exists>x. P x y"
proof
  fix y
  show "\<exists>x. P x y" 
  proof - 
    from A obtain x where "\<forall>y. P x y" by blast
    hence "P x y" by blast
    thus "\<exists>x. P x y" by blast
  qed      
qed


lemma assumes A: "\<exists>x. \<forall>y. P x y" shows "\<forall>y. \<exists>x. P x y"
proof
  fix y
  from A obtain x where 1: "P x y" by blast
  show "\<exists>x. P x y" proof
    show "P x y" by fact
  qed      
qed    
  
  
  
(* Witness for existential can only contain variables that were 
  fixed BEFORE exI rule was applied! 
  
  Try starting proof above with 
    proof (intro allI exI)
  
*)
  
  


section{* Streamlining proofs *}

subsection{* Pattern matching and ?-variables *}

text{* Show EX *}

lemma "\<exists> xs. length xs = 0" (is "\<exists> xs. ?P xs")
proof
  show "?P []" by simp
qed

text{* Multiple EX *}

lemma "\<exists> x y :: int. x < z & z < y" (is "\<exists> x y. ?P x y")
proof (intro exI)
  show "?P (z - 1) (z + 1)" by arith
qed

(* Forward proof *)
lemma "\<exists> x y :: int. x < z & z < y" (is "\<exists> x y. ?P x y")
proof -
  have "?P (z - 1) (z + 1)" by arith
  thus ?thesis by blast
qed


subsection{* Quoting facts: *}

lemma assumes "x < (0::int)" shows "x*x > 0"
proof -
  thm \<open>x<0\<close>
  from `x<0` show ?thesis by(metis mult_neg_neg)
qed


subsection {* Example: Top Down Proof Development *}

lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) \<or>
  (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  assume "even (length xs)" 
  then obtain n where A: "length xs = n+n"
    by (metis dvdE mult_2)
  hence W1: "xs = take n xs @ drop n xs" by simp
  have W2: "length (take n xs) = length (drop n xs)" by (simp add: A)
  from W1 W2 show ?thesis by blast
next      
  assume "odd (length xs)" thus ?thesis sorry
qed  


subsection {* moreover *}

lemma assumes "A \<and> B" shows "B \<and> A"
proof -
  from `A \<and> B` have "A" by auto
  moreover
  from `A \<and> B` have "B" by auto
  ultimately show "B \<and> A" by auto
qed


subsection{* Raw proof blocks *}

lemma fixes k :: int assumes "k dvd (n+k)" shows "k dvd n"
proof -
  { fix a assume a: "n+k = k*a"
    have "EX b. n = k*b"
    proof
      show "n = k*(a - 1)" using a by(simp add: algebra_simps)
    qed } 
  with assms show ?thesis by (auto simp add: dvd_def)
qed

subsection{* Local Lemmas. Shortcut for raw proof block with name *}

lemma fixes k :: int assumes "k dvd (n+k)" shows "k dvd n"
proof -
  have AUX: "EX b. n = k*b" if a: "n+k = k*a" for a
  proof
    show "n = k*(a - 1)" using a by(simp add: algebra_simps)
  qed 
  with assms show ?thesis by (auto simp add: dvd_def)

  thm AUX (* Local lemma also available by its name *)
qed




section{* Solutions to interactive exercises *}

lemma assumes "\<exists>x. \<forall>y. P x y" shows "\<forall>y. \<exists>x. P x y"
proof
  fix b
  from assms obtain a where 0: "\<forall>y. P a y" by blast
  show "\<exists>x. P x b"
  proof
    show "P a b" using 0 by blast
  qed
qed

lemma fixes x y :: real assumes "x \<ge> y" "y > 0"
shows "(x - y) ^ 2 \<le> x^2 - y^2"
proof -
  have "(x - y) ^ 2 = x^2 + y^2 - 2*x*y"
    by(simp add: numeral_eq_Suc algebra_simps)
  also have "\<dots> \<le> x^2 + y^2 - 2*y*y"
    using assms by(simp)
  also have "\<dots> = x^2 - y^2"
    by(simp add: numeral_eq_Suc)
  finally show ?thesis .
qed

subsection {* Example: Top Down Proof Development *}

text{* The key idea: case distinction on length: *}

lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) \<or>
  (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  assume "EX n. length xs = n+n"
  show ?thesis sorry
next
  assume "\<not> (EX n. length xs = n+n)"
  show ?thesis sorry
qed

text{* A proof skeleton: *}

lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) \<or>
  (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  assume "\<exists>n. length xs = n+n"
  then obtain n where "length xs = n+n" by blast
  let ?ys = "take n xs"
  let ?zs = "take n (drop n xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs" sorry
  thus ?thesis by blast
next
  assume "\<not> (\<exists>n. length xs = n+n)"
  then obtain n where "length xs = Suc(n+n)" sorry
  let ?ys = "take (Suc n) xs"
  let ?zs = "take n (drop (Suc n) xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" sorry
  then show ?thesis by blast
qed

text{* The complete proof: *}

lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) \<or>
  (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  assume "\<exists>n. length xs = n+n"
  then obtain n where "length xs = n+n" by blast
  let ?ys = "take n xs"
  let ?zs = "take n (drop n xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs"
    by (simp add: `length xs = n + n`)
  thus ?thesis by blast
next
  assume "\<not> (\<exists>n. length xs = n+n)"
  hence "\<exists>n. length xs = Suc(n+n)" by arith
  then obtain n where l: "length xs = Suc(n+n)" by blast
  let ?ys = "take (Suc n) xs"
  let ?zs = "take n (drop (Suc n) xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" by (simp add: l)
  thus ?thesis by blast
qed

end
