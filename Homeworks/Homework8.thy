theory Homework8
imports "../Tutorials/IMPArrayHoarePartial"
begin
  context includes IMP_Syntax begin
  
  (*
    ISSUED: Wednesday, Nov 8
    DUE: Wednesday, Nov 15, 11:59pm
    POINTS: 10 (3+3+4) and 4 bonus points
  *)
  
  
  (*
    General remark: 
      If you cannot discharge all verification conditions (VCs), single them 
      out and use sorry only on that specific VC! 
      Sometimes sledgehammer might help, and sometimes your invariant may 
      just be too weak. It might make sense to try to prove the VC on paper,
      and then translate your paper proof to an Isar proof, 
      or try to figure out why the VC is not provable and alter the 
      invariant accordingly.
  
      In case of odd-looking problems with the VCG, do not hesitate to 
      contact me, it might actually be a bug in the VCGs setup, as you are 
      the first people to use it ;) 
      Most often, it will be a forgotten variable binding or CLR, though!
      
  *)
  
  section \<open>Part 1\<close>
    (*
      Warm-up: Division by approximation from below.
    *)

    (* Hint: The following lemma might be useful to discharge a proof obligation! *)
    lemma div1_aux: "\<lbrakk>(0::int) \<le> n\<^sub>0; q\<^sub>0 \<noteq> 0; \<not> r * q\<^sub>0 \<le> n\<^sub>0; (r - 1) * q\<^sub>0 \<le> n\<^sub>0\<rbrakk> \<Longrightarrow> r - 1 = n\<^sub>0 div q\<^sub>0"
      by (smt Divides.pos_mod_sign cancel_div_mod_rules(2) mult.commute mult_right_mono_neg nonzero_mult_div_cancel_right zdiv_mono1)
      
    
    abbreviation "div_prog \<equiv> 
      CLR r;; 
      r ::= N 1;;
      WHILE ($r * $q <= $n) DO (
        r ::= Plus ($r) (N 1)
      );;
      r ::= Minus ($r) (N 1)
      "
  
    definition Idiv :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" 
      where "Idiv n\<^sub>0 q\<^sub>0 r \<equiv> (0 \<le> n\<^sub>0) \<and>((r-1)*q\<^sub>0) \<le> n\<^sub>0"  (* Provide an invariant! *)
      
lemma div_aux: " 0 \<le> n\<^sub>0 \<Longrightarrow> q\<^sub>0 \<noteq> 0 \<Longrightarrow> r * q\<^sub>0 \<le> n\<^sub>0 \<Longrightarrow> Idiv n\<^sub>0 q\<^sub>0 r \<Longrightarrow> Idiv n\<^sub>0 q\<^sub>0 (r + 1)"
" 0 \<le> n\<^sub>0 \<Longrightarrow> q\<^sub>0 \<noteq> 0 \<Longrightarrow> \<not> r * q\<^sub>0 \<le> n\<^sub>0 \<Longrightarrow> Idiv n\<^sub>0 q\<^sub>0 r \<Longrightarrow> r - 1 = n\<^sub>0 div q\<^sub>0"
"0 \<le> n\<^sub>0 \<Longrightarrow> q\<^sub>0 \<noteq> 0 \<Longrightarrow> Idiv n\<^sub>0 q\<^sub>0 1"
   apply (simp add: Idiv_def)  
  using Idiv_def div1_aux apply blast
  by (simp add: Idiv_def)
    
    lemma "\<lbrakk>0\<le>n\<^sub>0; q\<^sub>0\<noteq>0\<rbrakk> \<Longrightarrow>                          (* Precondition *)  
      \<Turnstile> {\<lambda>s. s ''n'' = var n\<^sub>0 \<and> s ''q'' = var q\<^sub>0}   (* Input variable binding *)  
          div_prog 
        {\<lambda>s. 
          \<exists>r. s ''r'' = var r                       (* Output variable bindings *) 
          \<and> s ''n'' = var n\<^sub>0 \<and> s ''q'' = var q\<^sub>0     (* Unchanged variables *)
          \<and> r = n\<^sub>0 div q\<^sub>0 }"                        (* Postconditions *)
          
      apply (rewrite annot_invar[where 
        I="\<lambda>s. \<exists>r. s ''r'' = var r                  (* Variables changed in the loop *)
            \<and> s ''n'' = var n\<^sub>0 \<and> s ''q'' = var q\<^sub>0   (* Unchanged variables *) 
            \<and> Idiv n\<^sub>0 q\<^sub>0 r                          (* Logical invariant *)
        "]) 
      supply div_aux[simp]
      apply vcg
      done  
  
  section \<open>Part 2\<close>
  
    (*
      Slightly more complex: discrete 2's logarithm!
      
      Approximation from below, combined with 
      iteratively computing \<open>a = 2^r\<close>.
    *)
  
    abbreviation "log2_prog \<equiv> 
      CLR r;; CLR a;;
      r ::= N 1;;
      a ::= N 2;;
      WHILE ($a <= $n) DO (
        a ::= $a * N 2;;
        r ::= Plus ($r) (N 1)
      );;
      r ::= Minus ($r) (N 1)
      "

 schematic_goal [simplified]: "(log2_prog,<''n'':=var 2>) \<Rightarrow> ?s"
  by BigSteps
  
    definition Ilog2 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where 
      "Ilog2 n\<^sub>0 a r \<equiv> 2^ nat (r) = a \<and> 
                      2^ nat (r-1) \<le> n\<^sub>0 \<and> 
                      n\<^sub>0 \<ge>0 \<and> r\<ge>1"  (* Provide an invariant! *)
      
      
lemma log2_aux: "1 \<le> n\<^sub>0 \<Longrightarrow> Ilog2 n\<^sub>0 2 1"
                "1 \<le> n\<^sub>0 \<Longrightarrow> \<not> a \<le> n\<^sub>0 \<Longrightarrow> Ilog2 n\<^sub>0 a r \<Longrightarrow> 2 ^ nat (r - 1) \<le> n\<^sub>0 \<and> n\<^sub>0 < 2 ^ nat r"
                "1 \<le> n\<^sub>0 \<Longrightarrow> a \<le> n\<^sub>0 \<Longrightarrow> Ilog2 n\<^sub>0 a r \<Longrightarrow> Ilog2 n\<^sub>0 (a * 2) (r + 1)"
supply nat_add_distrib[simp]
apply (auto simp:Ilog2_def algebra_simps) 
done
    
    lemma "1\<le>n\<^sub>0 \<Longrightarrow>                    
      \<Turnstile> {\<lambda>s. s ''n'' = var n\<^sub>0}         
          log2_prog 
        {\<lambda>s. 
          \<exists>r. s ''r'' = var r \<and> s ''n'' = var n\<^sub>0
          \<and> 2^nat r \<le> n\<^sub>0 \<and> n\<^sub>0 < 2^nat (r+1) }"  
      (* 
        Come up with the variable bindings in the invariant yourself! 
        See explanation and examples in tutorial! *)
      apply (rewrite annot_invar[where 
        I="\<lambda>s. 
           \<exists>r a. s ''r'' = var r \<and> s ''a'' = var a
           \<and> s ''n'' = var n\<^sub>0 
           \<and> Ilog2  n\<^sub>0 a r "]) 
        supply log2_aux[simp]
      apply vcg
      done
  
  section \<open>Part 3\<close>
  
    (*
      Do it yourself: Factorial for positive numbers.
      Only the specification is given, you must come up with the program,
      and prove it correct.
      
      Use a counting-up algorithm, then it's unlikely 
      that you need to prove additional properties of \<open>ifact\<close>!
    *)  
    definition ifact :: "int \<Rightarrow> int" where "ifact n = (\<Prod>i=1..n. i)"
    
    lemma ifact_simp[simp]: "0\<le>(i::int) \<Longrightarrow> {1..1 + i} = insert (i+1) {1..i}" by auto
    
    (*
      These are the recursion equations for the integer factorial:
    *)  
    lemma ifact_simps[simp]:
      "i\<ge>0 \<Longrightarrow> ifact (i+1) = (i+1)*ifact i"
      "i\<ge>0 \<Longrightarrow> ifact (1+i) = (1+i)*ifact i"
      "i\<le>0 \<Longrightarrow> ifact i = 1"
      unfolding ifact_def
      by (auto simp: algebra_simps)

    lemma ifact_nonzero[simp]: "ifact n\<^sub>0 \<noteq> 0" unfolding ifact_def by auto
      
    value "ifact 5"
    
    (*
      The following program uses a counting-up loop to compute the factorial.
    *)  
abbreviation "fact_prog \<equiv> 
  CLR r;; CLR a;;
  r ::= N 1;;
  a ::= N 0;;
  WHILE ($a < $n ) DO(
    a ::= Plus ($a) (N 1);;
    r ::= Times ($r) ($a)

  )

" (* Do not forget to CLR your auxiliary and output variables!*)
definition Ifact :: "int \<Rightarrow> int \<Rightarrow> int\<Rightarrow> bool" where 
  "Ifact n\<^sub>0 r a \<equiv> (r = ifact a) \<and> 
                   r\<ge>1 \<and> 
                   n\<^sub>0\<ge>0 \<and> 
                   a\<ge>0 \<and> a \<le> n\<^sub>0 "  
    (* Prove it correct! Find an invariant, and use the VCG. *) 
lemma ifact_aux: " 0 \<le> n\<^sub>0 \<Longrightarrow> Ifact n\<^sub>0 1 0"
    by (auto simp: Ifact_def algebra_simps)
    
lemma ifact_aux2: " 0 \<le> n\<^sub>0 \<Longrightarrow> \<not> a < n\<^sub>0 \<Longrightarrow> Ifact n\<^sub>0 r a \<Longrightarrow> r = ifact n\<^sub>0"
  by (auto simp: Ifact_def algebra_simps)
 
lemma ifact_aux3: "0 \<le> n\<^sub>0 \<Longrightarrow> a < n\<^sub>0 \<Longrightarrow> Ifact n\<^sub>0 r a \<Longrightarrow> Ifact n\<^sub>0 (r * (a + 1)) (a + 1)"
  apply (auto simp: Ifact_def)
  by (smt zero_less_mult_iff)
  
    lemma "0\<le>n\<^sub>0 \<Longrightarrow> 
      \<Turnstile> {\<lambda>s. s ''n'' = var n\<^sub>0 } 
           fact_prog 
        {\<lambda>s. \<exists>r. s ''r'' = var r \<and> s ''n'' = var n\<^sub>0 \<and> r = (ifact n\<^sub>0) }"
              
      apply (rewrite annot_invar[where 
        I="\<lambda>s. \<exists>r a. s ''r'' = var r \<and> s ''a'' = var a   (* Variables changed in the loop *)
            \<and> s ''n'' = var n\<^sub>0                          (* Unchanged variables *) 
            \<and> (Ifact n\<^sub>0 r a)                                  (* Logical invariant *)
        "])
      supply ifact_aux[simp]
      supply ifact_aux2[simp]
      supply ifact_aux3[simp]
      apply vcg 
      done
       
      
  section \<open>Bonus\<close>
      
    (* Now you are on your own! Bonus homework!
    
      Implement an IMP-program to compute the Fibonacci numbers, and
      show that it is correct.
      
      Do not forget to Clear any non-input variable that you use!
      
      Warning: You may run into some problems with conversions 
        between integers and natural numbers. In this case, try to go to Isar,
        and/or prove adequate auxiliary lemmas. Also sledgehammer may help.
    *)  
      
    (* These are the Fibonacci numbers *)
    
    fun fib :: "nat \<Rightarrow> nat" where 
      "fib 0 = 1"
    | "fib (Suc 0) = 1"  
    | "fib (Suc (Suc n)) = fib n + fib (Suc n)"  
      
    (* A postcondition for integers might contain something like *)
    prop \<open>0\<le>n\<^sub>0 \<and> r = int (fib (nat n\<^sub>0))\<close>
    
    (* Write a program *)
abbreviation "fib_prog \<equiv> 
CLR r1;; CLR r2;;CLR r;;CLR c;;
r1::= N 1;;
r2::= N 1;;
r::=  N 1;;
c ::= N 1;;
WHILE ($c < $n)DO(
    r  ::= Plus ($r1) ($r2);;
    r1 ::= $r2;;
    r2 ::= $r;;
    c  ::= Plus ($c) (N 1) 
)
"
  
  schematic_goal [simplified]: "(fib_prog,<''n'':=var 2>) \<Rightarrow> ?s"
  by BigSteps
  
  definition Ifib :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" 
    where "Ifib c n\<^sub>0 r r1 r2 \<equiv> 1 \<le> c  \<and> 
                               0 \<le> n\<^sub>0 \<and>
                               r \<ge> 1  \<and> 
                               r1 \<ge> 1 \<and> r2 \<ge> 1 \<and> r1\<le>r2 \<and> 
                               (if c >1 \<and> n\<^sub>0 \<ge>c then r = r1+r2 else r = 1)"
    
     
 lemma fib_aux: " 0 \<le> n\<^sub>0 \<Longrightarrow> c < n\<^sub>0 \<Longrightarrow> Ifib c n\<^sub>0 r r1 r2 \<Longrightarrow> Ifib (c + 1) n\<^sub>0 (r1 + r2) r2 (r1 + r2)"  
  apply (auto simp:Ifib_def)
sorry
    
 lemma fib_aux1: "0 \<le> n\<^sub>0 \<Longrightarrow> \<not> c < n\<^sub>0 \<Longrightarrow> Ifib c n\<^sub>0 r r1 r2 \<Longrightarrow> r = int (fib (nat n\<^sub>0))"  
  apply (auto simp:Ifib_def)  
   sorry
     
lemma fib_aux2: " 0 \<le> n\<^sub>0 \<Longrightarrow> Ifib 1 n\<^sub>0 1 1 1"
apply (auto simp:Ifib_def)  
 done  
    (* Come up with a reasonable specification and prove it correct! *)
lemma "0\<le>n\<^sub>0 \<Longrightarrow>
  \<Turnstile> {\<lambda>s.  s ''n'' = var n\<^sub>0} 
      fib_prog 
    {\<lambda>s. 
    \<exists>r. s ''r'' = var r
    \<and>  s ''n'' = var n\<^sub>0 
    \<and> 0\<le>n\<^sub>0 \<and> r = int (fib (nat n\<^sub>0))}"
  
    apply (rewrite annot_invar[where 
    I="\<lambda>s. \<exists>r r1 r2 c. s ''r'' = var r \<and>s ''r1'' = var r1 \<and>s ''r2'' = var r2  \<and>s ''c'' = var c    (* Variables changed in the loop *)
        \<and> s ''n'' = var n\<^sub>0        (* Unchanged variables *) 
        \<and> Ifib c n\<^sub>0 r r1 r2          (* Logical invariant *)
    "])
    supply fib_aux[simp]
    supply fib_aux1[simp]
    supply fib_aux2[simp]
    apply vcg
    done
    
        
  
  end
end
