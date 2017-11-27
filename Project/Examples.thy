chapter \<open>Examples for IMP++\<close>
theory Examples
imports IPP_Lib "~~/src/HOL/Library/Multiset"
begin

locale Imp_Array_Examples begin
  unbundle IMP_Syntax          -- \<open>Syntactic Sugar for IMP Programs. Unbundling this may take some time.\<close>
  sublocale Vcg_Aux_Lemmas .   -- \<open>Library of auxiliary lemmas commonly needed for verification\<close>
end  
  
context Imp_Array_Examples begin

section \<open>Common Loop Patterns\<close>
subsection \<open>Approximate from Below\<close>
text \<open>Used to invert a monotonic function. 
  We count up, until we overshoot the desired result, 
  then we subtract one. 
\<close>  

definition "sqrt_prog \<equiv> 
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
  "\<lbrakk>0 \<le> n\<^sub>0; \<not> r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> 0 < r"
  apply (auto simp: Isqrt_def power2_eq_square algebra_simps)
  by (smt combine_common_factor mult_right_mono semiring_normalization_rules(3))
  
find_theorems "(_(_:=_)) _"

lemma "                    
  \<Turnstile>\<^sub>t {\<lambda>n\<^sub>0. vars n in n=n\<^sub>0 \<and> 0\<le>n\<^sub>0}           
      sqrt_prog 
    {\<lambda>n\<^sub>0. vars r n in n=n\<^sub>0 \<and> 0\<le>r \<and> r\<^sup>2 \<le> n\<^sub>0 \<and> n\<^sub>0 < (r+1)\<^sup>2} mod {''r''}"
  unfolding sqrt_prog_def
  
  apply (rewrite annot_tinvar[where 
    R="measure (\<lambda>s. nat (s ''n'' 0 + 1 - s ''r'' 0))" and
    I="\<lambda>n\<^sub>0. vars r n in n=n\<^sub>0 \<and> 0\<le>n\<^sub>0 \<and> Isqrt n\<^sub>0 r
    "]) 
  supply Isqrt_aux [simp]
  by vcg
  
subsection \<open>Count Up\<close>  

text \<open>
  Counter \<open>c\<close> counts from \<open>0\<close> to \<open>n\<close>, such that loop is executed \<open>n\<close> times.
\<close>

subsubsection \<open>Exponential\<close>
definition "exp_prog \<equiv> 
  CLR c;; CLR r;;  
  c ::= N 0;;
  r ::= N 1;;
  WHILE $c < $n DO (
    r ::= $r * $b;;
    c ::= $c + (N 1)
  )"

text \<open>The invariant states that we have computed the function for the counter value \<open>c\<close>:\<close>  
  
abbreviation "Iexp n\<^sub>0 b\<^sub>0 r c \<equiv> 0\<le>c \<and> c\<le>n\<^sub>0 \<and> r = b\<^sub>0 ^ nat c"
  
lemma "                                
  \<Turnstile>\<^sub>t {\<lambda>(n\<^sub>0,b\<^sub>0). vars n b in n=n\<^sub>0 \<and> b=b\<^sub>0 \<and> 0\<le>n\<^sub>0}  
       exp_prog 
     {\<lambda>(n\<^sub>0,b\<^sub>0). vars r n b in n=n\<^sub>0 \<and> b=b\<^sub>0 \<and> r = b\<^sub>0 ^ nat n\<^sub>0} mod {''c'',''r''}"
  unfolding exp_prog_def   
  apply (rewrite annot_tinvar[where 
    R="measure (\<lambda>s. nat (s ''n'' 0 - s ''c'' 0))" and 
    I="\<lambda>(n\<^sub>0,b\<^sub>0). vars r c n b in n=n\<^sub>0 \<and> b=b\<^sub>0 \<and> Iexp n\<^sub>0 b\<^sub>0 r c"])
  apply vcg 
  done

subsubsection \<open>Factorial\<close>

definition ifact :: "int \<Rightarrow> int" where "ifact n = (\<Prod>i=1..n. i)"

lemma [simp]: "0\<le>(i::int) \<Longrightarrow> {1..1 + i} = insert (i+1) {1..i}" by auto

lemma ifact_simps[simp]:
  "i\<ge>0 \<Longrightarrow> ifact (i+1) = (i+1)*ifact i"
  "i\<ge>0 \<Longrightarrow> ifact (1+i) = (1+i)*ifact i"
  "i\<le>0 \<Longrightarrow> ifact i = 1"
  unfolding ifact_def
  by (auto simp: algebra_simps)

lemma ifact_nonzero[simp]: "ifact n\<^sub>0 \<noteq> 0" unfolding ifact_def by auto
  
abbreviation "fact_prog \<equiv> 
  CLR r;; CLR c;;
  r ::= N 1;;
  c ::= N 0;;
  WHILE ($c < $n) DO (
    c ::= $c + N 1;;
    r ::= $r * $c    
  )"
  
definition "fact_invar n r c \<equiv> 0\<le>c \<and> c\<le>n \<and> r=ifact c"  

lemma fact_prog_correct: " 
  \<Turnstile>\<^sub>t {\<lambda>n\<^sub>0. vars n in n=n\<^sub>0 \<and> 0\<le>n } 
       fact_prog 
    {\<lambda>n\<^sub>0. vars n r in n=n\<^sub>0 \<and> r = (ifact n\<^sub>0) } mod {''r'',''c''}"
  apply (rewrite annot_tinvar[where 
    I="\<lambda>n\<^sub>0. vars n r c in n=n\<^sub>0 \<and> fact_invar n\<^sub>0 r c"
  and R="measure_exp ($n - $c)"  
    ])
  unfolding fact_invar_def
  by vcg
  
  
subsubsection \<open>Square by Sum\<close>

text \<open>We exploit the fact that \<open>n\<^sup>2\<close> is the sum of the first \<open>n\<close> odd numbers.
  We compute the next odd number in the loop, in auxiliary variable \<open>b\<close>.
\<close>

definition "sqr_prog \<equiv> 
  CLR a;; CLR b;; CLR c;;
  b ::= \<acute>1;;
  a ::= \<acute>0;;
  c ::= \<acute>0;;
  WHILE ($c < $n) DO (
    a ::= $a + $b;;
    b ::= $b + \<acute>2;;
    c ::= $c + \<acute>1
  )"

lemma sqr_prog_correct: 
  "\<Turnstile>\<^sub>t {\<lambda>_. vars n in n\<ge>0} sqr_prog {\<lambda>_. vars n a in a=n\<^sup>2} mod {''a'', ''b'', ''c''}"
  unfolding sqr_prog_def
  apply (rewrite annot_tinvar[where R="measure_exp ($n-$c)" 
        and I="\<lambda>_. vars a b c n in a=c\<^sup>2 \<and> b = 2*c+1 \<and> c\<le>n"])
  apply vcg_all
  apply (auto simp: power2_eq_square algebra_simps)
  done


  
  
  
subsubsection \<open>Fibonacci Numbers\<close>  
fun fib :: "nat \<Rightarrow> nat" where 
  "fib 0 = 1"
| "fib (Suc 0) = 1"  
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"  
      
    
abbreviation "fib_prog \<equiv> 
  CLR j;; CLR k;; CLR c;;
  j::=N 1;;
  k::=N 1;;
  c::=N 1;;
  
  WHILE $c < $n DO (
    CLR t;;
    t::=$k;; k::=$k+$j;; j::=$t;;
    c::=$c + N 1
  )
"

lemma fib_aux: "0 < c \<Longrightarrow> fib (nat c) + fib (nat (c - 1)) = fib (Suc (nat c))"
  by (smt Suc_nat_eq_nat_zadd1 add.commute fib.simps(3))

lemma fib_correct: "
  \<Turnstile> {\<lambda>_. vars n in 0\<le>n } 
      fib_prog 
    {\<lambda>_. vars n k in k = int (fib (nat n))} mod {''c'', ''j'', ''k'', ''t''}"
  apply (rewrite annot_invar[where I="\<lambda>_. vars j k c n in 
       0<c \<and> 0\<le>n
    \<and> (0<n \<longrightarrow> c\<le>n \<and> j=int (fib (nat (c-1))) \<and> k = int (fib (nat c)))
    \<and> (n=0 \<longrightarrow> k=1)
  "])
  supply fib_aux[simp]
  by vcg
  
  
subsection \<open>Count down\<close>  
  
subsubsection \<open>Exponential\<close>
text \<open>Essentially the same as count up, but we use the input variable as counter\<close>

definition "exp_prog' \<equiv> 
  CLR r;;  (* Aux variables are cleared before use. *)
  r ::= N 1;;
  WHILE N 0 < $n DO (
    r ::= $r * $b;;
    n ::= $n - N 1
  )"

  
lemma [simp]: "lhs_vars exp_prog' = {''n'',''r''}"
  by (simp add: exp_prog'_def)

  
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
    
      
lemma exp_prog'_vcs:  
  "\<lbrakk>0 \<le> n\<^sub>0; 0 < n; exp_invar' n\<^sub>0 b\<^sub>0 n r\<rbrakk> \<Longrightarrow> exp_invar' n\<^sub>0 b\<^sub>0 (n - 1) (r * b\<^sub>0)"
  "\<lbrakk>0 \<le> n\<^sub>0; \<not> 0 < n; exp_invar' n\<^sub>0 b\<^sub>0 n r\<rbrakk> \<Longrightarrow> r = b\<^sub>0 ^ nat n\<^sub>0"
  "0 \<le> n\<^sub>0 \<Longrightarrow> exp_invar' n\<^sub>0 b\<^sub>0 n\<^sub>0 1"
  by (auto simp: exp_invar'_def) 

lemma exp_prog'_correct: " 
  \<Turnstile>\<^sub>t {\<lambda>(n\<^sub>0,b\<^sub>0). vars n b in n=n\<^sub>0 \<and> b=b\<^sub>0 \<and> 0\<le>n\<^sub>0} 
       exp_prog' 
    {\<lambda>(n\<^sub>0,b\<^sub>0). vars r b in b=b\<^sub>0 \<and> r = (b\<^sub>0 ^ nat n\<^sub>0)} mod {''r'',''n''}"
proof -
  note [simp] = exp_prog'_vcs
  show ?thesis
    unfolding exp_prog'_def   
    apply (rewrite annot_tinvar[where 
      I="\<lambda>(n\<^sub>0,b\<^sub>0). vars r n b in b=b\<^sub>0 \<and> exp_invar' n\<^sub>0 b\<^sub>0 n r \<and> 0\<le>n\<^sub>0" and
      R="measure (\<lambda>s. nat (s ''n'' 0))"
      ])
    by vcg 
qed    


subsubsection \<open>Square by Sum\<close>
definition "sqr_prog' \<equiv> 
  CLR a;; CLR b;; 
  b ::= \<acute>1;;
  a ::= \<acute>0;;
  WHILE (\<acute>0 < $n) DO (
    a ::= $a + $b;;
    b ::= $b + \<acute>2;;
    n ::= $n - \<acute>1
  )"

lemma sqr_prog'_correct: 
  "\<Turnstile>\<^sub>t {\<lambda>n\<^sub>0. vars n in n=n\<^sub>0 \<and> 0\<le>n\<^sub>0} sqr_prog' {\<lambda>n\<^sub>0. vars a in a=n\<^sub>0\<^sup>2} mod {''a'',''b'',''n''}"
  unfolding sqr_prog'_def
  apply (rewrite annot_tinvar[where R="measure_exp ($n)" 
        and I="\<lambda>n\<^sub>0. vars a b n in 0\<le>n \<and> n\<le>n\<^sub>0 \<and> (let i=n\<^sub>0-n in b=2*i+1 \<and> a=i\<^sup>2)"])
  apply vcg_all
  apply (auto simp: power2_eq_square algebra_simps)
  done


subsubsection \<open>Factorial\<close>
definition "fact_prog' \<equiv> 
  CLR r;;
  r ::= N 1;;
  WHILE ($n > N 0) DO (
    r ::= $r * $n;;
    n ::= $n - N 1
  )"

definition fact'_invar :: "int \<Rightarrow> _" 
  where "fact'_invar n\<^sub>0 n r \<equiv> r = ifact n\<^sub>0 div ifact n \<and> 0\<le>n \<and> n\<le>n\<^sub>0"
  

lemma ifact_div_one_less:
  assumes "0 < n" "n \<le> n\<^sub>0"
  shows "ifact n\<^sub>0 div ifact (n - 1) = ifact n\<^sub>0 div ifact n * n"
proof -
  have [simp]: "finite B \<Longrightarrow> 0\<notin>A \<Longrightarrow> A\<subseteq>B \<Longrightarrow> \<Prod>B div \<Prod>A = \<Prod>(B-A)" for A B :: "int set"
    by (simp add: prod.subset_diff rev_finite_subset)
  have [simp]: "0<n \<Longrightarrow> n\<le>n\<^sub>0 \<Longrightarrow> ({1..n\<^sub>0} - {1..n - 1}) = insert n ({1..n\<^sub>0} - {1..n})"
    by auto

  from assms show ?thesis
    unfolding ifact_def by auto
qed      
  
lemma fact'_vcs:  
  "0 \<le> n\<^sub>0 \<Longrightarrow> fact'_invar n\<^sub>0 n\<^sub>0 1"
  "\<lbrakk>0 < n; fact'_invar n\<^sub>0 n r\<rbrakk> \<Longrightarrow> fact'_invar n\<^sub>0 (n - 1) (r * n)"
  "\<lbrakk>\<not> 0 < n; fact'_invar n\<^sub>0 n r\<rbrakk> \<Longrightarrow> r = ifact n\<^sub>0"
  by (auto simp: fact'_invar_def ifact_div_one_less) 

lemma fact'_correct: " 
  \<Turnstile>\<^sub>t {\<lambda>n\<^sub>0. vars n in n=n\<^sub>0 \<and> 0\<le>n}
       fact_prog' 
    {\<lambda>n\<^sub>0. vars r in r = (ifact n\<^sub>0) } mod {''n'',''r''}"
  unfolding fact_prog'_def  
  apply (rewrite annot_tinvar[where 
      R="measure_exp ($n)"
    and I="\<lambda>n\<^sub>0. vars r n in fact'_invar n\<^sub>0 n r
  "])
  supply [simp] = fact'_vcs
  by vcg


section \<open>Reusing Programs in Context\<close>

declare exp_prog'_correct[vcg_rules]

fun (in -) tower2 :: "nat \<Rightarrow> nat" where 
  "tower2 0 = 1"
| "tower2 (Suc n) = 2^tower2 n"

definition "tower2_prog \<equiv> 
  CLR b;; CLR c;; CLR a;; 
  b ::= \<acute>2;;
  c ::= \<acute>0;;
  a ::= \<acute>1;;
  WHILE $c < $x DO (
    CLR n;;
    n::=$a;;
    exp_prog';;
    a::=$r;;
    c::=$c+\<acute>1
  )" 
  
lemma tower2_prog_correct: "\<Turnstile>\<^sub>t 
  {\<lambda>x\<^sub>0. vars x in x=x\<^sub>0 \<and> 0\<le>x} 
    tower2_prog 
  {\<lambda>x\<^sub>0. vars x a in x=x\<^sub>0 \<and> a=int (tower2 (nat x))} mod {''b'',''c'',''a'',''n'',''r''}"
  unfolding tower2_prog_def
  apply (rewrite annot_tinvar[where
    R = "measure_exp ($x-$c)" and
    I = "\<lambda>x\<^sub>0. vars b c a x in x=x\<^sub>0 \<and> 0\<le>c \<and> c\<le>x \<and> b=2 \<and> a = int (tower2 (nat c))"
  ])
  by vcg


  
  
section \<open>Working with Arrays\<close>  
  
subsection \<open>Summation over Array\<close>

definition "array_sum \<equiv> 
  CLR r;;             
  r ::= N 0;;         
  WHILE $l < $h DO (
    r ::= $r + a\<^bold>[$l\<^bold>];;
    l ::= $l + (\<acute>1)
  )"


lemma array_sum_aux:
  fixes f :: "int \<Rightarrow> int"
  shows "l\<^sub>0\<le>l \<Longrightarrow> (\<Sum>i=l\<^sub>0..<l+1. f i) = (\<Sum>i=l\<^sub>0..<l. f i) + f l" 
  by (auto simp: intvs_incdec)
  
lemma "\<Turnstile> 
  {\<lambda>l\<^sub>0. vars l h (a:imap) in l\<le>h \<and> l=l\<^sub>0 } 
    Imp_Array_Examples.array_sum 
  {\<lambda>l\<^sub>0. vars l h (a:imap) r in r = (\<Sum>i=l\<^sub>0..<h. a i) } mod {''l'',''r''}
  "
  unfolding array_sum_def
  apply (rewrite annot_invar[where 
    I="\<lambda>l\<^sub>0. vars l h (a:imap) r in
      l\<^sub>0\<le>l \<and> l\<le>h
      \<and> r = (\<Sum>i=l\<^sub>0..<l. a i)"])
  supply array_sum_aux[simp]    
  by vcg

text \<open>Getting rid of the \<open>l\<le>h\<close> precondition\<close>

lemma array_sum_correct: "\<Turnstile> 
  {\<lambda>l\<^sub>0. vars l h (a:imap) in l=l\<^sub>0 } 
    array_sum 
  {\<lambda>l\<^sub>0. vars l h (a:imap) r in r = (\<Sum>i=l\<^sub>0..<h. a i) } mod {''l'',''r''}"
  unfolding array_sum_def
  apply (rewrite annot_invar[where 
    I="\<lambda>l\<^sub>0. vars l h (a:imap) r in (
        if l\<^sub>0 \<le> h then  
            l\<^sub>0 \<le>l
          \<and> l \<le> h 
          \<and> r = (\<Sum>i\<in>{l\<^sub>0..<l}. a i)
        else
            r = 0 
          \<and> l = l\<^sub>0
        )
        "])
  supply array_sum_aux[simp]    
  supply if_splits[split]        
  by vcg

text \<open>Summing up only elements greater 5\<close>  
  
definition "array_sum_gt5 \<equiv> 
  CLR r;;
  r ::= N 0;;
  WHILE $l < $h DO (
    IF N 5 < a\<^bold>[$l\<^bold>] THEN
      r ::= $r + a\<^bold>[$l\<^bold>]
    ELSE SKIP;;  
    l ::= $l + N 1
  )"
    
abbreviation "gt5 i \<equiv> if i>5 then i else 0"  
  
lemma array_sum_gt5_correct: "\<Turnstile> 
  {\<lambda>l\<^sub>0. vars l h (a:imap) in l=l\<^sub>0}
    array_sum_gt5 
  {\<lambda>l\<^sub>0. vars h (a:imap) r in r = (\<Sum>i\<in>{l\<^sub>0..<h}. gt5 (a i)) } mod {''r'',''l''}" 
  unfolding array_sum_gt5_def
  apply (rewrite annot_invar[where 
    I="\<lambda>l\<^sub>0. vars (a:imap) h l r in
      (
        if l\<^sub>0 \<le> h then 
          l\<^sub>0\<le>l
          \<and> l\<le>h
          \<and> r = (\<Sum>i\<in>{l\<^sub>0..<l}. gt5 (a i))
        else
            r = 0 
          \<and> l = l\<^sub>0
      )
        "])
  supply array_sum_aux[simp]    
  supply if_splits[split]        
  by vcg


subsection \<open>Range of an Array as List\<close>  
function (sequential) lran :: "(int \<Rightarrow> val) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> val list" where
  "lran a l h = (if l<h then a l # lran a (l+1) h else [])"
  by pat_completeness auto
termination 
  by (relation "measure (\<lambda>(_,l,h). nat (h-l))") auto
  
declare lran.simps[simp del]  
  
text \<open>
  \<open>lran a l h\<close> is the list \<open>[a\<^sub>l,a\<^sub>l\<^sub>+\<^sub>1,...,a\<^sub>h\<^sub>-\<^sub>1]\<close>
\<close>

subsubsection \<open>Auxiliary Lemmas\<close>

lemma lran_empty[simp]: 
  "lran a l l = []"
  "lran a l h = [] \<longleftrightarrow> h\<le>l"
  by (rewrite lran.simps; auto)+

lemma lran_bwd_simp: "lran a l h = (if l<h then lran a l (h-1)@[a (h-1)] else [])"
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  apply (rewrite in "_ = \<hole>" lran.simps)
  by (auto simp: less_le)
    
    
lemma lran_append1[simp]: "l\<le>h \<Longrightarrow> lran a l (h + 1) = lran a l h @ [a h]"
  by (rewrite in "\<hole> = _" lran_bwd_simp) auto

lemma lran_prepend1[simp]: "l\<le>h \<Longrightarrow> lran a (l-1) h = a(l-1) # lran a l h"
  by (rewrite in "\<hole> = _" lran.simps) auto
    
lemma lran_tail[simp]: "lran a (l+1) h = tl (lran a l h)"
  apply (rewrite in "_ = \<hole>" lran.simps)
  apply auto
  done
    
lemma lran_butlast[simp]: "lran a l (h-1) = butlast (lran a l h)"
  apply (rewrite in "_ = \<hole>" lran_bwd_simp)
  apply auto
  done
  

lemma lran_upd_outside[simp]:
  "i<l \<Longrightarrow> lran (a(i:=x)) l h = lran a l h"
  "h\<le>i \<Longrightarrow> lran (a(i:=x)) l h = lran a l h"
  subgoal
    apply (induction a l h rule: lran.induct)
    apply (rewrite in "\<hole> = _" lran.simps)
    apply (rewrite in "_ = \<hole>" lran.simps)
    by (auto)
  subgoal
    apply (induction a l h rule: lran.induct)
    apply (rewrite in "\<hole> = _" lran.simps)
    apply (rewrite in "_ = \<hole>" lran.simps)
    by (auto)
  done  

lemma lran_eq_iff: "lran a l h = lran a' l h \<longleftrightarrow> (\<forall>i. l\<le>i \<and> i<h \<longrightarrow> a i = a' i)"  
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  apply (rewrite in "_ = \<hole>" lran.simps)
  apply auto
  by (metis antisym_conv not_less zless_imp_add1_zle)
  
lemma set_lran[simp]: "set (lran a l h) = a`{l..<h}"  
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  apply auto
  by (metis atLeastLessThan_iff image_iff not_less not_less_iff_gr_or_eq zless_imp_add1_zle)
  
lemma mset_lran[simp]: "mset (lran a l h) = image_mset a (mset_set {l..<h})"
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  by (auto simp: intvs_lower_incr)

subsection \<open>Filtering\<close>
definition "filter_prog \<equiv>
  CLR r;; CLR w;;
  r::=$l;; w::=$l;;
  WHILE $r<$h DO (
    IF a\<^bold>[$r\<^bold>] > \<acute>5 THEN
      a\<^bold>[$w\<^bold>] ::= a\<^bold>[$r\<^bold>];;
      w::=$w+\<acute>1
    ELSE SKIP;;
    r::=$r+\<acute>1
  );;
  h::=$w
  "  

lemma filter_prog_correct: " 
  \<Turnstile>\<^sub>t {\<lambda>(h\<^sub>0,a\<^sub>0). vars l h (a:imap) in a=a\<^sub>0 \<and> h=h\<^sub>0 \<and> l\<le>h} 
       filter_prog 
     {\<lambda>(h\<^sub>0,a\<^sub>0). vars l h (a:imap) in h\<le>h\<^sub>0 \<and> lran a l h = filter (\<lambda>x. 5<x) (lran a\<^sub>0 l h\<^sub>0)}
     mod {''h'', ''r'', ''w'', ''a''}
     "
  unfolding filter_prog_def   
  apply (rewrite annot_tinvar[where 
    I="\<lambda>(h\<^sub>0,a\<^sub>0). vars l h (a:imap) r w in 
      h=h\<^sub>0 \<and> l\<le>w \<and> w\<le>r \<and> r\<le>h \<and>
      lran a l w = filter (\<lambda>x. 5<x) (lran a\<^sub>0 l r) \<and>
      lran a r h = lran a\<^sub>0 r h
      "
    and
    R="measure_exp ($h - $r)"
    ])
  supply lran_eq_iff[simp]
  by vcg

subsection \<open>Find First Element in Range\<close>  
  definition "find_in_range_prog \<equiv> 
    WHILE $l<$h && a\<^bold>[$l\<^bold>] != $x DO l::=$l+\<acute>1
  "    
  
  abbreviation "iran_spec l h a x \<equiv> (
    let
      iran = \<lambda>i. i\<in>{l..<h} \<and> a i = x  (* i is in range and points to x *)
    in
      (if \<exists>i. iran i then 
        (LEAST i. iran i)    (* Return least index *)
       else h                (* Or upper bound to indicate that no element has been found *)
      )
    )"
  
  lemma find_in_range_prog_correct: "
    \<Turnstile> {\<lambda>l\<^sub>0. vars l h x (a : imap) in l=l\<^sub>0 \<and> l\<le>h}
      find_in_range_prog
    {\<lambda>l\<^sub>0. vars l h x (a : imap) in l = iran_spec l\<^sub>0 l a x } mod {''l''}"
    unfolding find_in_range_prog_def
    apply (rewrite annot_invar[where I="\<lambda>l\<^sub>0.
      vars l h x (a : imap) in  
        l\<^sub>0\<le>l \<and> l\<le>h \<and> (\<forall>i\<in>{l\<^sub>0..<l}. a i \<noteq> x)"])
    apply vcg_all
    apply (auto simp: Let_def)
    done
  
subsection \<open>Minimum Sort\<close>  
  
subsubsection \<open>Find Minimum\<close>
  
text \<open>Find index of minimum element in \<open>a i, ..., a (h-1)\<close>, return in \<open>j\<close>\<close>
definition "find_min \<equiv> 
  CLR j;; CLR k;; CLR m;;
  j::=$i;; k::=$i+\<acute>1;; m::=a\<^bold>[$j\<^bold>];;
  WHILE $k<$h DO (
    (* m stores current minimum element, j stores its index *)
    IF a\<^bold>[$k\<^bold>] < $m THEN
      m ::= a\<^bold>[$k\<^bold>];;
      j::=$k
    ELSE SKIP;;
    k::=$k+\<acute>1
  )"
  
  
lemma [simp]: "lhs_vars find_min 
  = {''k'', ''j'', ''m''}"  
  unfolding find_min_def by auto
  
(* Augment the type signature as long as no type variables ('a,'b,...) occur 
  in the output of the definition command! *)  
definition find_min_invar :: "int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> _"
  where
  "find_min_invar i h a j k m \<equiv> 
      i\<le>j \<and> j<h \<and> i<k \<and> k\<le>h            (* Everything in range *)
    \<and> m = a j \<and> a j = Min (a`{i..<k})"  (* m stores minimum element, j its index *) 

lemma fmi_vcs_aux1: "i\<^sub>0 < k \<Longrightarrow> \<forall>x\<in>{i\<^sub>0..<k}. a\<^sub>0 k < (a\<^sub>0::int\<Rightarrow>int) x \<Longrightarrow> a\<^sub>0 k = Min (a\<^sub>0 ` {i\<^sub>0..<k + 1})"  
  apply (rule Min_eqI[symmetric])
  apply (auto simp: Ball_def) 
  using eq_iff by fastforce
  
lemma fmi_vcs:
  "\<lbrakk>k < h; find_min_invar i h a j k m; a k < m\<rbrakk> \<Longrightarrow> find_min_invar i h a k (k + 1) (a k)"
  "\<lbrakk>k < h; find_min_invar i h a j k m; \<not> a k < m\<rbrakk> \<Longrightarrow> find_min_invar i h a j (k + 1) m"
  "\<lbrakk>\<not> k < h; find_min_invar i h a j k m\<rbrakk> \<Longrightarrow> i \<le> j \<and> j < h \<and> a j = Min (a ` {i..<h})"
  "i < h \<Longrightarrow> find_min_invar i h a i (i + 1) (a i)"
  unfolding find_min_invar_def
  apply (simp_all add: fmi_vcs_aux1)
  subgoal 
    apply (clarsimp simp add: intvs_incdec min_def not_less)
    apply (rule Min_eqI)
    apply auto 
    by (metis atLeastLessThan_iff eq_iff image_eqI)
  done  


lemma find_min_correct[vcg_rules]: "\<Turnstile>\<^sub>t
  {\<lambda>_. vars i h (a:imap) in i<h} 
    find_min 
  {\<lambda>_. vars i h (a:imap) j in i\<le>j \<and> j<h \<and> (a j = Min (a`{i..<h}))} 
  mod {''j'',''k'',''m''}"
  unfolding find_min_def
  apply (rewrite annot_tinvar[where 
    R="measure_exp ($h - $k)" and
    I="\<lambda>_. vars i h (a:imap) j k m in find_min_invar i h a j k m"
  ])
  apply vcg_all

  (* If the VCs make the simplifier loop, some more 'creative' techniques may help.
  
    using fmi_vcs by metis+
  
    Or, apply them one by one!
  *)
  using fmi_vcs(1) apply metis
  using fmi_vcs(2) apply metis
  using fmi_vcs(3) apply metis
  using fmi_vcs(3) apply metis
  using fmi_vcs(3) apply metis
  using fmi_vcs(4) apply metis
  done
  
  
subsubsection \<open>Minsort Algorithm\<close>  
text \<open>Sort the array \<open>a\<close> in between indices \<open>l\<close> and \<open>h\<close>.
  Idea: Find minimum element in remaining part array,
    swap to end of already sorted part.
    
    \<open>i\<close> points to first element of unsorted part.
\<close>  
definition "minsort \<equiv> 
  CLR i;;
  i::=$l;;
  WHILE $i<$h DO (
    find_min;;
  
    CLR t;;
    t ::= a\<^bold>[$i\<^bold>];;
    a\<^bold>[$i\<^bold>] ::= a\<^bold>[$j\<^bold>];;
    a\<^bold>[$j\<^bold>] ::= $t;;
    
    i::=$i+\<acute>1
  )"
  
  
definition "sorted_spec l l' \<equiv> mset l' = mset l \<and> sorted l'"
  
(* verify that all types are inferred as int, and no polymorphic ('a) types remain! *)
definition "I_minsort a\<^sub>0 l\<^sub>0 h\<^sub>0 a i \<equiv> 
    l\<^sub>0\<le>i \<and> i\<le>h\<^sub>0 
  \<and> mset (lran a\<^sub>0 l\<^sub>0 h\<^sub>0) = mset (lran a l\<^sub>0 h\<^sub>0)   (* Array contains original elements *)
  \<and> sorted (lran a l\<^sub>0 i)                        (* Sorted part is sorted *)
  \<and> (\<forall>k1\<in>{l\<^sub>0..<i}. \<forall>k2\<in>{i..<h\<^sub>0}. a k1 \<le> a k2)  (* Every element of unsorted part \<ge> sorted part *)
  "


lemma [simp]: "lhs_vars minsort = {''i'', ''a'', ''t'', ''k'', ''j'', ''m''}"
  unfolding minsort_def by auto

lemma image_mset_subst_outside: "x\<notin>#s \<Longrightarrow> image_mset (f(x:=y)) s = image_mset f s"
  by (induction s) auto

lemma image_mset_subst_in_range:
  assumes "i\<in>{l::int..<h}"  
  shows "image_mset (f(i:=x)) (mset_set {l..<h}) = image_mset f (mset_set {l..<h}) - {#f i#} + {#x#}"
proof -  
  from assms have "l<h" "l\<le>i" "i<h" by auto
  then show ?thesis
    apply (induction rule: int_less_induct)
    apply (auto simp: intvs_decr_l image_mset_subst_outside)
    apply (simp add: antisym_conv)
    done
qed    
  
  
  
lemma minsort_vcs:  
  "\<lbrakk>I_minsort z l ha aa ia; ia \<le> j; j < ha; aa j = Min (aa ` {ia..<ha})\<rbrakk>
       \<Longrightarrow> I_minsort z l ha (aa(ia := Min (aa ` {ia..<ha}), j := aa ia)) (ia + 1)"
  "\<lbrakk>\<not> i < h; I_minsort z l h a i\<rbrakk> \<Longrightarrow> sorted_spec (lran z l h) (lran a l h)"
  "l \<le> h \<Longrightarrow> I_minsort z l h z l"  
  subgoal
    unfolding I_minsort_def
    apply (auto simp: sorted_append)
    apply (metis fun_upd_triv)
    apply (auto simp: image_mset_subst_in_range)
    done
  subgoal
    unfolding I_minsort_def sorted_spec_def
    by (auto)

  subgoal
    unfolding I_minsort_def
    by (auto)
  
  done
  
  
lemma minsort_correct: "\<Turnstile>\<^sub>t
  {\<lambda>a\<^sub>0. vars l h (a:imap) in l\<le>h \<and> a=a\<^sub>0}
    minsort
  {\<lambda>a\<^sub>0. vars l h (a:imap) in sorted_spec (lran a\<^sub>0 l h) (lran a l h) } 
    mod {''i'',''t'',''j'',''k'',''m'',''a''}"
  
  unfolding minsort_def
  apply (rewrite annot_tinvar[where 
    R = "measure_exp ($h - $i)" and
    I = "\<lambda>a\<^sub>0. vars l h (a:imap) i in I_minsort a\<^sub>0 l h a i"
    ])
  supply minsort_vcs[simp]  
  by vcg
  
  
  
section \<open>Debugging\<close>  
text \<open>Automatic Derivation of Big-Step Execution\<close>
  fun vlist' :: "int \<Rightarrow> val list \<Rightarrow> (int \<Rightarrow> val)" where
    "vlist' l [] = (\<lambda>_. 0)"
  | "vlist' l (x#xs) = (vlist' (l+1) xs)(l:=x)"
  
  abbreviation "vlist \<equiv> vlist' 0"
  
  schematic_goal "(array_sum,<''l'':=var 1, ''h'':=var 5, ''a'':=vlist [100,1,2,3,4,200,300]>) \<Rightarrow> ?s"
    unfolding array_sum_def
    by BigSteps

  schematic_goal "(fact_prog',<''n'' := var 5>) \<Rightarrow> ?s"  
    unfolding fact_prog'_def
    by BigSteps
  
  
    
    
end
  

end
