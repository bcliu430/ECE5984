theory Auto_Proof_Demo
imports Main
begin

term "{x::int. x>0}"  
  
term "{x+y | x y. x>0 \<and> y>0}"
  
  
lemma "{x+y :: int | x y. x>0 \<and> y>0} = {x. x>1}"  
  apply auto
  by presburger 
    
  
section{* Logic and sets *}

lemma "\<forall>x. \<exists>y. x=y"
  by auto
    
term "()"    
    
lemma "\<exists>x::unit. \<forall>y. x=y" by simp
  
lemma "\<exists>x. True" by blast
    

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
by auto

text{* Note the bounded quantification notation: *}

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys;  us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n+n"
by fastforce

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys;  us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n+n"
  try0
  by fastforce

  
  
text{*
 Most simple proofs in FOL and set theory are automatic.
 Example: if T is total, A is antisymmetric
 and T is a subset of A, then A is a subset of T.
*}

lemma AT:
  "\<lbrakk> \<forall>x y. T x y \<or> T y x;
     \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
     \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
   \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
by blast


section{* Sledgehammer *}

lemma "R^* \<subseteq> (R \<union> S)^*"
  by (simp add: rtrancl_mono)

(* Find a suitable P and try sledgehammer: *)

lemma lemma1: "a # xs = ys @ [a] \<Longrightarrow> xs=[] \<and> ys=[] \<or> (\<exists>zs. xs=zs@[a] \<and> ys=a#zs)"
  by (metis Cons_eq_append_conv list.inject)
    
(* Can you also show equivalence ? *)    
lemma "a # xs = ys @ [a] \<longleftrightarrow> (xs=[] \<and> ys=[] \<or> (\<exists>zs. xs=zs@[a] \<and> ys=a#zs))"
  by (meson Cons_eq_append_conv lemma1)
    
lemma "{x::int. x>0} \<subseteq> {x. x>-3}" 
  apply safe
  by auto  
    
thm lemma1    
    

section{* Arithmetic *}

lemma "\<lbrakk> (a::int) \<le> f x + b; 2 * f x < c \<rbrakk> \<Longrightarrow> 2*a + 1 \<le> 2*b + c"
by arith

lemma "\<forall> (k::nat) \<ge> 8. \<exists> i j. k = 3*i + 5*j"
by arith

lemma "(n::int) mod 2 = 1 \<Longrightarrow> (n+n) mod 2 = 0"
by arith

lemma "(i + j) * (i - j) \<le> i*i + j*(j::int)"
by (simp add: algebra_simps)

lemma "(5::int) ^ 2 = 20+5"
by simp

end
