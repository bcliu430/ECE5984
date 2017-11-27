theory Homework7
imports 
  "../IMP/Small_Step" 
  "~~/src/HOL/Library/Code_Target_Nat"   (* Makes value-command compute with ML-integers rather than unary Suc (Suc ...) objects. *)
begin


  (*
    ISSUED: Wednesday, Nov 1
    DUE: Wednesday, Nov 8, 11:59pm
    POINTS: 10   (5 per part)
  *)


  (********** PART 1 ***************)

  (*
    In this homework, we will develop a faster way to interpret programs.
  
    First, we want to define a functional version of a small step,
    that is, a function 
      small_stepf :: com * state \<Rightarrow> (com * state) option
    that returns the next configuration, after performing one small step.
    If the configuration was final, it shall return None.
    The equations of this function correspond to the rules of SmallStep.
    
    Complete the function!
  *)



  (* Hint: Ignore *warnings* about ambiguous inputs ... the \<Rightarrow> in case and big-step causes them.
    If you get type *errors*, though, DO NOT IGNORE THEM!
  *)

  fun small_stepf :: "com * state \<Rightarrow> (com * state) option" where
    "small_stepf (x ::= a, s) = Some (SKIP, s(x := aval a s))"
  | "small_stepf (SKIP;;c\<^sub>2,s) = Some (c\<^sub>2,s)"
  | "small_stepf (c\<^sub>1;;c\<^sub>2,s) = undefined"
  | "small_stepf (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) = undefined"
        (* Note: Although there are two If-rules in SmallStep, you only need a single equation here!  *)
  | "small_stepf (WHILE b DO c,s) = undefined"
  | "small_stepf _ = None" (* Catch-all case*)

  (* Show that small_stepf indeed computes a single small step! *)
  lemma small_stepf_eq: "cs\<rightarrow>cs'\<longleftrightarrow> small_stepf cs = Some cs'" sorry

  (* Show that None is returned only for final configurations.
    Hint: Already implied by thm small_stepf_eq, no separate induction required!
  *)
  lemma final_eq: "final cs \<longleftrightarrow> small_stepf cs = None"
    sorry
    

  (* 
    Write a function iterate that iterates small_stepf, until a final 
    configuration is reached, but for at most n iterations.
    
    If no final configuration is reached after n iterations, the function 
    shall return None. 
    
    Hint: For n=0, it is OK to always return None, even if the configuration should be final.
      This will simplify the equation for 0.
  
    n is also called fuel: Each iteration uses one unit of fuel, 
      and when running out of fuel the computation stops.
      
    Do not use \<rightarrow> or final in your function, but 
    use small_stepsf instead (cf. thms small_stepf_eq and final_eq)!
      
  *)  
  fun iterate :: "nat \<Rightarrow> com * state \<Rightarrow> (com * state) option" where
    "iterate 0 cs = undefined"
  | "iterate (Suc n) cs = undefined"
  
  (* Show that iterate behaves as expected! 
    There is a terminating execution if, and only if, there is an 
    initial fuel value such that iterate returns Some.
    
    Hint: Prove both directions separately.
  *)
  lemma iterate_eq: "(cs \<rightarrow>* cs' \<and> final cs') \<longleftrightarrow> (\<exists>n. iterate n cs = Some cs')"
    sorry
    
  (*
    The iterate function gives you another way to execute programs, which 
    is considerably faster than constructing derivation trees.
    
    Notes: 
      * the extracts the value cs from Some cs, and the None is undefined.
      * snd extracts the second component of a pair
      * If you do not specify enough initial fuel, the command will just return 
        \<open>snd (the None) ''a''\<close>, otherwise it returns teh correct result, e.g., 225.
        Specifying too much fuel, on the other hand, is no problem, as the iteration 
        stops once it reaches a final result, not necessarily using up all its fuel.
  
  *)

  value "(snd (the (iterate 100000000000 (DerTreeExample.square,<''x'':=15>)))) ''a''"

  
  (********** PART 2 ***************)
  
  (*
    In this part, you are supposed to write some programs, 
    satisfying a given specification. Test your programs!
    
    Try to find short and simple programs that only use the 
    available operations of IMP!
  *)
  
  
  (* Write a program power2 that returns 2^c (2 to the power of c) in variable a.
    You may assume c being non-negative.
  
    Specification: { c=i\<^sub>c \<and> i\<^sub>c\<ge>0 } power2 { a=2^i\<^sub>c }, i\<^sub>c does not occur in power2!
  *)

  definition power2 where "power2 \<equiv> undefined"
    
  (* Template for testing \<dots> *)
  value "(snd (the (iterate 100000000000 (power2,<''c'':=10>)))) ''a''"
    
  (* If you did not succeed with the iterate function, use the standard big-step
    derivation to test your programs ... will be much slower, though!
  *)
  schematic_goal "(power2,<''c'':=10>) \<Rightarrow> ?s"
    unfolding power2_def
    by BigSteps
  
  
    
  (* Write a program that replaces variable a by a*b, and does not change b!
    You may assume that a and b are positive!
  
    Specification: { a=i\<^sub>a \<and> b=i\<^sub>b \<and> i\<^sub>a>0 \<and> i\<^sub>b>0 } mult { a=i\<^sub>a*i\<^sub>b \<and> b=i\<^sub>b }, i\<^sub>a,i\<^sub>b do not occur in mult!
  *)

  definition mult where "mult \<equiv> undefined
  "
  
  value "(snd (the (iterate 100000000000 (mult,<''a'':=10, ''b'':=7>)))) ''a''"

  (* Write a program that returns b^c in variable a. 
    You may assume that b is positive and c is non-negative
  
    Specification: { b=i\<^sub>b \<and> c=i\<^sub>c \<and> i\<^sub>b>0 \<and> i\<^sub>c\<ge>0 } power { a=i\<^sub>b^i\<^sub>c }, i\<^sub>b,i\<^sub>c do not occur in power
    
    Hint: Combine the ideas from the two above programs, you'll need two nested while loops.
      If your multiplication program uses auxiliary variables, keep care that they do not
      conflict with the variables used in your main program!
    
  *)
  
  definition power where "power \<equiv> undefined"
  
  value "(snd (the (iterate 100000000000 (power,<''b'':=5, ''c'':=4>)))) ''a''"
  
  
end
