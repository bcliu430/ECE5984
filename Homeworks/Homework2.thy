chapter \<open>Homework 2\<close>
theory Homework2
imports Main
begin
  
  (*
    This file is intended to be viewed within the Isabelle/jEdit IDE.
    In a standard text-editor, it is pretty unreadable!
  *)

  (*
    HOMEWORK #2
    RELEASED: Tue, Aug 19 2017
    DUE:      Tue, Aug 26, 2017, 11:59pm

    To be submitted via canvas.
  *)
  

section \<open>General Hints\<close>  
(*
  The best way to work on this homework is to fill in the missing gaps in this file.

  Try to go for simple function definitions, as simple definitions mean simple proofs!
  In particular, do not go for a more complicated definition only b/c it may be more efficient!


  The proofs should work with induction (structural/computations), 
  and some generalizations, followed by auto to solve the subgoals.
  You may have to add some simp-lemmas to auto, which we will hint at.
 
  We indicate were auxiliary lemmas are likely to be needed.
  However, as proofs depend on your definitions, we cannot predict every corner 
  case that you may run into. Changing the definition to something simpler might 
  help to get a simpler proof.


*)  
  

section \<open>For all elements in list\<close>    
  (* Define a function that checks wether a predicate P holds for all elements in a list.
     Note: A predicate is just a function of type "'a \<Rightarrow> bool". It must evaluate to True for all elements in the list.
  *)
  
  fun listall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
    "listall P [] \<longleftrightarrow> True" (* Return True for the empty list. *)
    (* Add your equation(s) here *)

  (* Show: P holds for all elements of xs@ys, if and only if it holds for all elements of xs and for all elements of ys: *)  
  lemma "listall P (xs@ys) \<longleftrightarrow> listall P xs \<and> listall P ys"  
    oops

  (* Show: When checking P for a  mapped list, we can also apply the function before we evaluate P *)    
  lemma "listall P (map f xs) = listall (\<lambda>x. P (f x)) xs"
    oops
  
  (* Specify and show: If we filter the list with P, all elements in the result will satisfy P.
    Note: In this exercise, you have to come up with both, the formula and the proof!
  *)    
  lemma "add your formula here and prove it" oops
  
  
section \<open>Sum of elements in a list\<close>  
  
(* Specify a function to sum up all elements in a list of integers. The empty list has sum 0. *)  
  
  fun listsum :: "int list \<Rightarrow> int" where
    "listsum _ = undefined"
    (* Replace by your equation(s) *)
  
  (* Show the following lemmas: *)

  (* Instead of summing over xs@ys, we can also add the results from summing over xs and summing over ys *)  
  lemma listsum_append: "listsum (xs@ys) = listsum xs + listsum ys"
    oops    
      
  (* Filtering out zeroes does not affect the sum *)    
  lemma listsum_filter_z: "listsum (filter (op\<noteq>0) l) = listsum l"  
    oops

  (* Reversing a list does not affect the sum. HINT: You'll need an auxiliary lemma. (that you already have proved) *)
  lemma listsum_rev: "listsum (rev xs) = listsum xs"    
    oops
    
  (* Specify and prove: If summing up a list with only non-negative numbers, the result will be non-negative: *)  
      
  lemma "add formula and prove it" oops
    
    
section \<open>Bonus: Delta-Encoding\<close>      
  (*
    We want to encode a list of integers as follows: 
      The first element is unchanged, and every next element 
      only indicates the difference to its predecessor.

      For example: (Hint: Use this as test cases for your spec!)
        enc [1,2,4,8] = [1,1,2,4]
        enc [3,4,5] = [3,1,1]
        enc [5] = [5]
        enc [] = []
      

      Background: This algorithm may be used in lossless data compression, 
        when the difference between two adjacent values is expected to be 
        small, e.g., audio data, image data, sensor data.

        It typically requires much less space to store the small deltas, than 
        the absolute values. 

        Disadvantage: If the stream gets corrupted, recovery is only possible 
          when the next absolute value is transmitted. For this reason, in 
          practice, one will submit the current absolute value from time to 
          time. (This is not modeled in this exercise!)



  *)
      
  
  (* Specify a function to encode a list with delta-encoding. 
    The first argument is used to represent the previous value, and can be initialized to 0.
  *)
  fun denc :: "int \<Rightarrow> int list \<Rightarrow> int list" where
    "denc _ _ = undefined"
    (* Replace by your equation(s) *)
  
  (* Specify the decoder. Again, the first argument represents the previous 
      decoded value, and can be initialized to 0. *)  
  fun ddec :: "int \<Rightarrow> int list \<Rightarrow> int list" where
    "ddec _ _ = undefined"
    (* Replace by your equation(s) *)
  
  (* Show that encoding and then decoding yields the same list. HINT: The lemma will need generalization. *)  
  lemma "ddec 0 (denc 0 l) = l" 
    oops
      
      
end
