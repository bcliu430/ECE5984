theory Tutorial4
imports IMPArrayHoarePartial
begin

context includes IMP_Syntax begin -- \<open>Use this to activate IMP Syntax\<close>

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

schematic_goal [simplified]: "(sqrt_prog,<''n'':=var 3>) \<Rightarrow> ?s"
  by BigSteps
  
  
text \<open>The invariant states that the \<open>r-1\<close> is not too big.
  When the loop terminates, \<open>r-1\<close> is not too big, but \<open>r\<close> is already too big,
  so \<open>r-1\<close> is the desired value (rounding down).
  
  Moreover, we have to state that \<open>0<r\<close>, otherwise, 
  we might get unsolvable goals (in the negative, incrementing \<open>r\<close> decreases \<open>r\<^sup>2\<close>!).
\<close>
definition Isqrt :: "int \<Rightarrow> int \<Rightarrow> bool" 
  where "Isqrt n\<^sub>0 r \<equiv> (r-1)\<^sup>2 \<le> n\<^sub>0"
  
text \<open>Note: Be careful to not accidentally define the invariant 
  over some generic type \<open>'a\<close>! \<close>  

lemma sqrt_aux:
  "0 \<le> n\<^sub>0 \<Longrightarrow> r * r \<le> n\<^sub>0 \<Longrightarrow> Isqrt n\<^sub>0 r \<Longrightarrow> Isqrt n\<^sub>0 (r + 1)"
  "0 \<le> n\<^sub>0 \<Longrightarrow> \<not> r * r \<le> n\<^sub>0 \<Longrightarrow> Isqrt n\<^sub>0 r \<Longrightarrow> (r - 1)\<^sup>2 \<le> n\<^sub>0 \<and> n\<^sub>0 < r\<^sup>2"
  "0 \<le> n\<^sub>0 \<Longrightarrow> Isqrt n\<^sub>0 1"
  by (auto simp: Isqrt_def power2_eq_square)
  
  

text \<open>The correctness statement has a canonical form:
  \<open>P i1\<^sub>0 \<dots> iN\<^sub>0 \<Longrightarrow>                                    (* Precondition*)   
    \<Turnstile> {\<lambda>s. 
        s ''i1'' = var i1\<^sub>0 \<and> \<dots> \<and> s ''iN'' = var iN\<^sub>0  (* Input variables *)
       }
      program
    {\<lambda>s. \<exists>o1 ... on. 
        s ''o1'' = var o1 \<and> \<dots> \<and> s ''oM'' = var oM    (* Output variables *)
      \<and> s ''u1'' = var u1\<^sub>0 \<and> ... \<and> s ''uK'' = var uK\<^sub>0 (* Unchanged variables*) 
      \<and> Q i1\<^sub>0 \<dots> iN\<^sub>0 o1 \<dots> oM                          (* Postcondition *)
    }  
  \<close>
  
  Here, the \<open>i1\<dots>iN\<close> are the input variables, 
  the \<open>o1\<dots>oM\<close> are the output variables,
  and the \<open>u1\<dots>uK \<subseteq> i1\<dots>iN\<close> are the input variables that do not change.
  
  Note that some input variables may change, and may be used as output variables.

  The precondition P and postcondition Q do not depend on the state, but only
  on the logical variables.
  
  
  Similar, invariants have the form:
    \<open>\<lambda>s. \<exists>x1...xN. 
        s ''x1'' = var x1 \<and> \<dots> \<and> s ''xM'' = var xM
      \<and> s ''u1'' = var u1 \<and> \<dots> \<and> s ''uK'' = var uK
      \<and> P i1\<^sub>0 \<dots> iN\<^sub>0  x1 \<dots> xM  u1 \<dots> uK
      
      where \<open>x1\<dots>xM\<close> are the variables that are changed in the loop,
      \<open>u1\<dots>uK\<close> are the variables that are not changed in the loop,
      and P is the invariant.
    \<close>
  
\<close>  
  
lemma "0\<le>n\<^sub>0 \<Longrightarrow>                  (* Precondition *)  
  \<Turnstile> {\<lambda>s. s ''n'' = var n\<^sub>0}       (* Input variable binding *)  
      sqrt_prog 
    {\<lambda>s. 
      \<exists>r. s ''r'' = var r         (* Output variable bindings *) 
      \<and> s ''n'' = var n\<^sub>0          (* Unchanged variables *)
      \<and> r\<^sup>2 \<le> n\<^sub>0 \<and> n\<^sub>0 < (r+1)\<^sup>2 }"  (* Postconditions *)
      
  apply (rewrite annot_invar[where 
    I="\<lambda>s. \<exists>r. s ''r'' = var r    (* Variables changed in the loop *)
        \<and> s ''n'' = var n\<^sub>0        (* Unchanged variables *) 
        \<and> Isqrt n\<^sub>0 r              (* Logical invariant *)
    "]) 
  supply sqrt_aux[simp]  
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
  
abbreviation Iexp :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where 
  "Iexp n\<^sub>0 b\<^sub>0 r c \<equiv> 0\<le>c \<and> c\<le>n\<^sub>0 \<and> r = b\<^sub>0 ^ nat c"
  
lemma "0\<le>n\<^sub>0 \<Longrightarrow>                                (* n must be non-negative *)
  \<Turnstile> {\<lambda>s. s ''n'' = var n\<^sub>0 \<and> s ''b'' = var b\<^sub>0}  (* Input in variables n and b *)
       exp_prog 
     {\<lambda>s. \<exists>r. s ''r'' = var r                  (* Output in r *)
      \<and> s ''n'' = var n\<^sub>0 \<and> s ''b'' = var b\<^sub>0    (* n and b unchanged *)
      \<and> r = b\<^sub>0 ^ nat n\<^sub>0}"                      (* Result will be b\<^sup>n *)
  apply (rewrite annot_invar[where I="\<lambda>s. 
    \<exists>r c. s ''r'' = var r \<and> s ''c'' = var c    (* Changed in the loop *)
    \<and> s ''n'' = var n\<^sub>0 \<and> s ''b'' = var b\<^sub>0      (* Unchanged *)
    
    \<and> Iexp n\<^sub>0 b\<^sub>0 r c                            (* Invariant *)
  "])
 (* supply nat_add_distrib[simp]*)
  apply vcg
  sorry

  
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
  where "exp_invar' n\<^sub>0 b\<^sub>0 n r \<equiv> let c = n\<^sub>0 - n in 
    0\<le>c \<and> c\<le>n\<^sub>0 \<and> r = b\<^sub>0 ^ nat c"

text \<open>If the invariants become more complex or hard to prove automatically,
  it can be advantageous to define the (logical part of) the invariant as
  a predicate, and prove the required VCs as separate lemmas.
\<close>  
    
lemma [simp]: "0\<le>n \<and> n\<le>n\<^sub>0 \<Longrightarrow> nat (n\<^sub>0 - (n - 1)) = Suc (nat (n\<^sub>0-n))"
  by linarith
      
lemma exp'_aux: 
  "0 \<le> n\<^sub>0 \<Longrightarrow> exp_invar' n\<^sub>0 b\<^sub>0 n\<^sub>0 1"
  "0 \<le> n\<^sub>0 \<Longrightarrow> 0 < n \<Longrightarrow> exp_invar' n\<^sub>0 b\<^sub>0 n r \<Longrightarrow> exp_invar' n\<^sub>0 b\<^sub>0 (n - 1) (r * b\<^sub>0)"
  "0 \<le> n\<^sub>0 \<Longrightarrow> \<not> 0 < n \<Longrightarrow> exp_invar' n\<^sub>0 b\<^sub>0 n r \<Longrightarrow> r = b\<^sub>0 ^ nat n\<^sub>0"
  by (auto simp: exp_invar'_def)
  
  
lemma "0\<le>n\<^sub>0 \<Longrightarrow> 
  \<Turnstile> {\<lambda>s. s ''n'' = var n\<^sub>0 \<and> s ''b'' = var b\<^sub>0} 
       exp_prog' 
    {\<lambda>s. \<exists>r. s ''r'' = var r \<and> s ''b'' = var b\<^sub>0 \<and> r = (b\<^sub>0 ^ nat n\<^sub>0)}"
proof -
  note [simp] = exp'_aux
  assume "0\<le>n\<^sub>0"
  then show ?thesis
    apply (rewrite annot_invar[where I="\<lambda>s. \<exists>r n.
        s ''n'' = var n 
      \<and> s ''b'' = var b\<^sub>0  
      \<and> s ''r'' = var r  
      \<and> exp_invar' n\<^sub>0 b\<^sub>0 n r
    "])
    apply vcg (* defer apply vcg_ctd defer apply vcg_ctd*)
    done
qed

end

end
