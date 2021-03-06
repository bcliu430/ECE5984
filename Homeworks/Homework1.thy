chapter \<open>Homework 1\<close>
theory Homework1
imports Main
begin
  (*
    This file is intended to be viewed within the Isabelle/jEdit IDE.
    In a standard text-editor, it is pretty unreadable!
  *)

  (*
    HOMEWORK #1
    RELEASED: Thu, Aug 7 2017
    DUE:      Thu, Aug 14, 2017, 2:00pm

    To be submitted via canvas.
  *)
  

section \<open>General Hints\<close>  
(*
  The best way to work on this homework is to fill in the missing gaps in this file,
  and then just submit your changed file via canvas.

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
  
 (* Replace the \<open>undefined\<close>s by some meaningful terms! *)  
  fun odd :: "nat \<Rightarrow> bool" where
    "odd 0 \<longleftrightarrow> undefined"
  | "odd (Suc n) \<longleftrightarrow> undefined"  
    
  
  (* Test cases. These should evaluate to True! *)
  value "odd 45"
  value "\<not>odd 42"
  
section \<open>Flattening of Nested Lists\<close>    
  (*  
    Write a function to flatten a list of lists, i.e., 
    concatenate all lists in the given list:
  *)  

  fun flatten :: "'a list list \<Rightarrow> 'a list" where
    "flatten [] = undefined"
  | "flatten (l#ls) = undefined"  

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
    (* Add the remaining equations! 
      Note: The function package will warn you about missing patterns, until you have added them all! *)    
      

  (* Returns the new carry *)  
  fun full_adder_c :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
    "full_adder_c False False False = False"
  | "full_adder_c False False True  = False" 
      (* Add the remaining equations! *)



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
    "to_nat [] = undefined"
  | "to_nat (True#bs) = undefined"  
  | "to_nat (False#bs) = undefined"  
    
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
    (* Standard case. Complete that! *)    
  | "addc (a#as) (b#bs) c = undefined"
    
    
  definition add :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list"
    where 
    "add as bs = undefined" (* Use addc here! *)
    

  (* Test Cases *)  
  value "add [True,True,False] [True,True,False] = [False,True,True]"
  value "add [True,False,True,False] [True,True,False,False] = [False, False, False, True]"  
  value "add [True,False,True,True] [True,True,False,False] = [False, False, False, False, True]"  
  value "addc [True,True,True] [True,False,True] True = [True, False, True, True]"  
      
    
section \<open>Bonus: Convert natural numbers to binary numbers\<close>      
      
  fun to_bin :: "nat \<Rightarrow> bool list" where
    "to_bin n = undefined" (* Insert meaningful equations here! Hints: odd, a div b *)
    
    
    
end
