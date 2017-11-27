chapter \<open>Examples for IMP with Arrays\<close>
theory IMPAHP_Examples
imports IMPArrayHoareTotal
begin
  
section \<open>Program Verification\<close>

context Imp_Array_Examples begin

subsection \<open>Common Loop Patterns\<close>

subsubsection \<open>Approximate from Below\<close>
text \<open>Used to invert a monotonic function. 
  We count up, until we overshoot the desired result, 
  then we subtract one. 
\<close>  

abbreviation "sqrt_prog \<equiv> 
  CLR r;; 
  r ::= N 1;;
  WHILE ($r * $r <= $n) DO (
    r ::= Plus ($r) (N 1)
  );;
  r ::= Minus ($r) (N 1)
  "

text \<open>The invariant states that the \<open>r-1\<close> is not too big.
  When the loop terminates, \<open>r-1\<close> is not too big, but \<open>r\<close> is already too big,
  so \<open>r-1\<close> is the desired value (rounding down).
\<close>
definition Isqrt :: "int \<Rightarrow> int \<Rightarrow> bool" 
  where "Isqrt n\<^sub>0 r \<equiv> 0\<le>r \<and> (r-1)\<^sup>2 \<le> n\<^sub>0"  
  
text \<open>Note: Be careful to not accidentally define the invariant 
  over some generic type \<open>'a\<close>! \<close>  
  
lemma Isqrt_aux:
  "0 \<le> n\<^sub>0 \<Longrightarrow> Isqrt n\<^sub>0 1"
  "\<lbrakk>0 \<le> n\<^sub>0; r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> Isqrt n\<^sub>0 (r + 1)"
  "\<lbrakk>0 \<le> n\<^sub>0; \<not> r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> (r - 1)\<^sup>2 \<le> n\<^sub>0 \<and> n\<^sub>0 < r\<^sup>2"
  "Isqrt n\<^sub>0 r \<Longrightarrow> r * r \<le> n\<^sub>0 \<Longrightarrow> r\<le>n\<^sub>0"
  apply (auto simp: Isqrt_def power2_eq_square algebra_simps)
  by (smt combine_common_factor mult_right_mono semiring_normalization_rules(3))
  
find_theorems "(_(_:=_)) _"

lemma "0\<le>n\<^sub>0 \<Longrightarrow>                    
  \<Turnstile>\<^sub>t {vars n in n=n\<^sub>0}           
      sqrt_prog 
    {vars r n in n=n\<^sub>0 \<and> r\<^sup>2 \<le> n\<^sub>0 \<and> n\<^sub>0 < (r+1)\<^sup>2}"
  apply (rewrite annot_tinvar[where 
    R="measure (\<lambda>s. nat (s ''n'' 0 + 1 - s ''r'' 0))" and
    I="vars r n in n=n\<^sub>0 \<and> Isqrt n\<^sub>0 r
    "]) 
  supply Isqrt_aux [simp]
  apply vcg
  done  

subsubsection \<open>Count up\<close>

text \<open>Count up to the desired value, and iteratively compute a function on the way\<close>
abbreviation "exp_prog \<equiv> 
  CLR c;; CLR r;;  
  c ::= N 0;;
  r ::= N 1;;
  WHILE $c < $n DO (
    r ::= $r * $b;;
    c ::= $c + (N 1)
  )"

text \<open>The invariant states that we have computed the function for value \<open>c\<close>:\<close>  
  
abbreviation "Iexp n\<^sub>0 b\<^sub>0 r c \<equiv> 0\<le>c \<and> c\<le>n\<^sub>0 \<and> r = b\<^sub>0 ^ nat c"
  
lemma "0\<le>n\<^sub>0 \<Longrightarrow>                                
  \<Turnstile>\<^sub>t {vars n b in n=n\<^sub>0 \<and> b=b\<^sub>0}  
       exp_prog 
     {vars r n b in n=n\<^sub>0 \<and> b=b\<^sub>0 \<and> r = b\<^sub>0 ^ nat n\<^sub>0}"
  apply (rewrite annot_tinvar[where 
    R="measure (\<lambda>s. nat (s ''n'' 0 - s ''c'' 0))" and 
    I="vars r c n b in n=n\<^sub>0 \<and> b=b\<^sub>0 \<and> Iexp n\<^sub>0 b\<^sub>0 r c"])
  supply nat_add_distrib[simp]
  apply vcg
  done

  
subsubsection \<open>Count down\<close>  
  
text \<open>Essentially the same as count up, but we use the input variable as counter\<close>

abbreviation "exp_prog' \<equiv> 
  CLR r;;  (* Aux variables are cleared before use. *)
  r ::= N 1;;
  WHILE N 0 < $n DO (
    r ::= $r * $b;;
    n ::= $n - N 1
  )"

text \<open>The invariant is the same as for count-up. 
  Only that we have to compute the actual number 
  of loop iterations by \<open>n\<^sub>0 - n\<close>
\<close>  
definition exp_invar' :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
  where "exp_invar' n\<^sub>0 b\<^sub>0 n r \<equiv> (
      let c=n\<^sub>0-n in
        0\<le>c \<and> c\<le>n\<^sub>0 \<and> r = b\<^sub>0 ^ nat c
    )"

text \<open>If the invariants become more complex or hard to prove automatically,
  it can be advantageous to define the (logical part of) the invariant as
  a predicate, and prove the required VCs as separate lemmas.
\<close>  
    
lemma [simp]: "0\<le>n \<and> n\<le>n\<^sub>0 \<Longrightarrow> nat (n\<^sub>0 - (n - 1)) = Suc (nat (n\<^sub>0-n))"
  by linarith
      
lemma aux1: "\<lbrakk>0 \<le> n\<^sub>0; 0 < n; exp_invar' n\<^sub>0 b\<^sub>0 n r\<rbrakk> \<Longrightarrow> exp_invar' n\<^sub>0 b\<^sub>0 (n - 1) (r * b\<^sub>0)"
  by (auto simp: exp_invar'_def) 
  
lemma aux2: "\<lbrakk>0 \<le> n\<^sub>0; \<not> 0 < n; exp_invar' n\<^sub>0 b\<^sub>0 n r\<rbrakk> \<Longrightarrow> r = b\<^sub>0 ^ nat n\<^sub>0"
  by (auto simp: exp_invar'_def) 
    
lemma aux3: "0 \<le> n\<^sub>0 \<Longrightarrow> exp_invar' n\<^sub>0 b\<^sub>0 n\<^sub>0 1"  
  by (auto simp: exp_invar'_def) 
  

lemma "0\<le>n\<^sub>0 \<Longrightarrow> 
  \<Turnstile>\<^sub>t {vars n b in n=n\<^sub>0 \<and> b=b\<^sub>0} 
       exp_prog' 
    {vars r b in b=b\<^sub>0 \<and> r = (b\<^sub>0 ^ nat n\<^sub>0)}"
proof -
  note [simp] = aux1 aux2 aux3
  assume "0\<le>n\<^sub>0"
  then show ?thesis
    apply (rewrite annot_tinvar[where 
      I="vars r n b in b=b\<^sub>0 \<and> exp_invar' n\<^sub>0 b\<^sub>0 n r" and
      R="measure (\<lambda>s. nat (s ''n'' 0))"
      ])
    by vcg 
qed    




abbreviation "sqr_prog \<equiv> 
  CLR a;; CLR b;; 
  b ::= \<acute>1;;
  a ::= \<acute>0;;
  WHILE (\<acute>0 < $n) DO (
    a ::= $a + $b;;
    b ::= $b + \<acute>2;;
    n ::= $n - \<acute>1
  )"

lemma "n\<^sub>0\<ge>0 \<Longrightarrow> \<Turnstile>\<^sub>t {vars n in n=n\<^sub>0} sqr_prog {vars a in a=n\<^sub>0\<^sup>2}"
  apply (rewrite annot_tinvar[where R="measure (\<lambda>s. nat (s ''n'' 0))" 
        and I="vars a b n in 0\<le>n \<and> n\<le>n\<^sub>0 \<and> (let i=n\<^sub>0-n in b=2*i+1 \<and> a=i\<^sup>2)"])
  apply vcg_all
  apply (auto simp: power2_eq_square algebra_simps)
  done


abbreviation "sqr_prog' \<equiv> 
  CLR a;; CLR b;; CLR c;;
  b ::= \<acute>1;;
  a ::= \<acute>0;;
  c ::= \<acute>0;;
  WHILE ($c < $n) DO (
    a ::= $a + $b;;
    b ::= $b + \<acute>2;;
    c ::= $c + \<acute>1
  )"

lemma "n\<^sub>0\<ge>0 \<Longrightarrow> \<Turnstile>\<^sub>t {vars n in n=n\<^sub>0} sqr_prog' {vars n a in n=n\<^sub>0 \<and> a=n\<^sub>0\<^sup>2}"
  apply (rewrite annot_tinvar[where R="measure (\<lambda>s. nat (s ''n'' 0 - s ''c'' 0))" 
        and I="vars a b c n in n=n\<^sub>0 \<and> a=c\<^sup>2 \<and> b = 2*c+1 \<and> c\<le>n\<^sub>0"])
  apply vcg_all
  apply (auto simp: power2_eq_square algebra_simps)
  done


  
end

end
