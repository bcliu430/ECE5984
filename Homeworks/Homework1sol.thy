chapter \<open>Homework 1\<close>
theory Homework1sol
imports Main
begin
  
  (*
    This file is intended to be viewed within the Isabelle/jEdit IDE.
    In a standard text-editor, it is pretty unreadable!
  *)

  (*
    HOMEWORK #1

    Sample solutions and comments

  *)
  

section \<open>General Hints\<close>  
(*
  The best way to work on this homework is to fill in the missing gaps in this file.

  All solutions are a few lines only, and do, unless indicated, not require 
  to define any auxiliary functions. So if you end up with 
  lengthy and complicated function definitions, you are probably just 
  missing an easier solution.

  Do not hesitate to show me your problems with your solutions, 
  eg, if Isabelle throws some cryptic error messages at you 
    that you cannot decipher ...


*)  
  
section \<open>Odd Natural Numbers\<close>  
  (*
    Write a function to return whether a given natural number is odd:
  *)
  
  fun odd :: "nat \<Rightarrow> bool" where
    "odd 0 \<longleftrightarrow> False"
  | "odd (Suc n) \<longleftrightarrow> \<not>odd n"
  
  (*

    I accepted every solution here that produced the right result,
    a common one was
      "odd (Suc n) \<longleftrightarrow> n mod 2 = 0"

    however, note, that you don't need pattern matching at all in this case, 
    and could, much simpler, write:
  *)  
    
  fun odd' :: "nat \<Rightarrow> bool" where "odd' n \<longleftrightarrow> n mod 2 = 1"  
    
    
    
    
  (* Test cases: *)  
  value "odd 45"
  value "\<not>odd 42"
  
section \<open>Flattening of Nested Lists\<close>    
  (*  
    Write a function to flatten a list of lists, i.e., 
    concatenate all lists in the given list:
  *)  

  fun flatten :: "'a list list \<Rightarrow> 'a list" where
    "flatten [] = []"
  | "flatten (l#ls) = l @ flatten ls"  

  (* 
    I ignored additions of superfluous stuff like "[]@l@flatten ls"
  *)  
    
  (* Test cases *)  
  value "flatten [[1::int,2],[],[3,4],[],[5]] = [1,2,3,4,5]"
  value "flatten [[],[],[],[1],[5]] = [1,5]"
    

section \<open>Full Adder\<close>    
  (*
    Recall that a full adder (Wikipedia has a nice entry on that) is a circuit that 
    takes three bits (two operands and a carry), and returns the 
    sum and the new carry.

    We model this as two functions, one for the sum and one for the new carry.
    Complete the function definitions!
  *)

  (* Returns the sum *)  
  fun full_adder_s :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
    "full_adder_s False False False = False"
  | "full_adder_s False False True  = True" 
  | "full_adder_s False True  False = True" 
  | "full_adder_s False True  True  = False" 
  | "full_adder_s True  False False = True" 
  | "full_adder_s True  False True  = False" 
  | "full_adder_s True  True  False = False" 
  | "full_adder_s True  True  True  = True" 
      

  (* Returns the new carry *)  
  fun full_adder_c :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
    "full_adder_c False False False = False"
  | "full_adder_c False False True  = False" 
  | "full_adder_c False True  False = False" 
  | "full_adder_c False True  True  = True" 
  | "full_adder_c True  False False = False" 
  | "full_adder_c True  False True  = True" 
  | "full_adder_c True  True  False = True" 
  | "full_adder_c True  True  True  = True"

    
  (*  
    Good demo that you can use pattern matching for encoding 
    truth-tables in a very readable way.
  *)  
    
section \<open>Binary Numbers as Lists of Booleans\<close>    
  (*
    We represent unsigned binary numbers as lists of Booleans.
    As addition goes from least to most significant bit, and 
    lists are best processed from head to tail, the first element 
    of the list is the least significant bit.

    For example:
      [True,False,True,True] represents the number 0b1101 = 13
      [False,False,True] represents 0b100 = 4

  *)  

  (* 
    Implement a function 
      to_nat :: bool list \<Rightarrow> nat 
    that returns the value of an unsigned binary number!
  *)  
  fun to_nat :: "bool list \<Rightarrow> nat" where
    "to_nat [] = 0"
  | "to_nat (True#bs) = 1 + 2*to_nat bs"  
  | "to_nat (False#bs) = 2*to_nat bs"  
    
  (*
    The trick was to see how one can use the recursive function call.
    This turned out to be a bit more difficult.
  *)  
    
    
    
  (* Test cases *)  
  value "to_nat [True,False,True,True] = 13"    
  value "to_nat [False,False,True] = 4"

section \<open>Adding Binary Numbers\<close>    
  (* 
    Implement a function add that adds two binary numbers. 
    Hint: Start with a function addc that adds to binary numbers 
        and takes an additional carry flag.

  *)  
    
  fun addc :: "bool list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> bool list" where
    (* Addition completed. In case of overflow, we just add another bit to our result *)
    "addc [] [] c = (if c then [True] else [])"
    (* Special cases if the numbers have different length *)
  | "addc (a#as) [] c = full_adder_s a False c # addc as [] (full_adder_c a False c)"  
  | "addc [] (b#bs) c = full_adder_s False b c # addc [] bs (full_adder_c False b c)"  
    (* Standard case *)    
  | "addc (a#as) (b#bs) c = full_adder_s a b c # addc as bs (full_adder_c a b c)"
    

  definition "add as bs = addc as bs False"  

  (*
    It was not too difficult to derive the last equation.
  *)  
    
    
  (* Test Cases *)  
  value "add [True,True,False] [True,True,False] = [False,True,True]"
  value "add [True,False,True,False] [True,True,False,False] = [False, False, False, True]"  
  value "add [True,False,True,True] [True,True,False,False] = [False, False, False, False, True]"  
  value "addc [True,True,True] [True,False,True] True = [True, False, True, True]"  
    
  (*
    By the way, if you wonder whether there is something meaningful to prove:
      You can show that your adder actually adds, wrt. your to_nat 
      interpretation. Unfortunately, the proof is a bit technical, 
      doing tons of case distinctions manually.
  *)  
    
  lemma addc_correct: 
    "to_nat (addc as bs c) = (to_nat as + to_nat bs + (if c then 1 else 0))"
    apply (induction as bs c rule: addc.induct)
    apply (auto split: if_splits)  
    apply (case_tac a; simp)  
    apply (case_tac a; simp)  
    apply (case_tac a; simp)  
    apply (case_tac a; simp)  
    apply (case_tac b; simp)  
    apply (case_tac b; simp)  
    apply (case_tac b; simp)  
    apply (case_tac b; simp)  
    apply (case_tac a; case_tac b; simp)  
    apply (case_tac a; case_tac b; simp)  
    apply (case_tac a; case_tac b; simp)  
    apply (case_tac a; case_tac b; simp)  
    done

  lemma add_correct: "to_nat (add as bs) = to_nat as + to_nat bs"
    using addc_correct[where c=False] unfolding add_def by auto
      
      
section \<open>Bonus: Convert natural numbers to binary numbers\<close>      
      
  fun to_bin :: "nat \<Rightarrow> bool list" where
    "to_bin 0 = []"
  | "to_bin n = (Parity.odd n # to_bin (n div 2))"  

  (*
    Unfortunately, I saw only few correct solutions to this one ... 
    all these did it like in the above, using either the odd function 
    from the homework, or, as I did, the one from the HOL library. 
    I had to refer to it by its long name "Parity.odd" as the short name "odd" 
    is hidden by the definition of "odd" in this theory file.
  *)
    

  (**
    Again, you can prove something: converting to bin, and then to 
      nat again should be identity. Note: The other way only holds if 
      the binary number is normalized, i.e. has no zero at most significant 
      position. 
  *)  
  lemma "to_nat (to_bin n) = n"
    apply (induction n rule: to_bin.induct)
    apply auto
    by (metis (full_types) Suc_eq_plus1_left even_Suc even_Suc_div_two 
        even_two_times_div_two to_nat.simps(2) to_nat.simps(3))
    
  (* The last line of the proof was actually automatically found by some advanced 
    proof search tool of Isabelle, which I will introduce later in the lecture, after
    the basics.
  *)
      
      
      
end
