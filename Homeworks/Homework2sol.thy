chapter \<open>Homework 2\<close>
theory Homework2sol
imports Main
begin
  
  (*
    This file is intended to be viewed within the Isabelle/jEdit IDE.
    In a standard text-editor, it is pretty unreadable!
  *)

  (*
    HOMEWORK #2 Sample solution and comments
  *)
  

section \<open>General Remarks\<close>  

(* Isabelle errors 

  Please try to avoid submitting theories with Isabelle errors!
*)  
  
(* Intentionally some Isabelle errors *)  
term "(0::int) = (0::nat)"
  
lemma True done  
    oops
  
fun f where "f x = f x"  
    
fun g :: "int \<Rightarrow> nat" where "g x = (x>5)"
  
(*
  Isabelle indicates errors by
    * a red squiggly line under the erroneous text
    * A red bar on the right side of the editor window, just next to the scrollbar
    * A red highlighting on the left hand side of the editor window, in the code folding and line-number area (if this is switched on for you)
    * A red highlighting in the theory panel

*)  
  
  
  
(* If you cannot finish a proof, end it with oops *)  
  
lemma "Suc n > 0 \<Longrightarrow> n>0"  
  apply auto
  (* No idea how to continue here \<dots>*)  
  oops  
  
(* If you need the lemma as auxiliary lemma for further proofs, and if 
  you are sure it holds, you only cannot prove it, then end the proof with 
  sorry, which will make Isabelle accept the lemma as true.
*)  

lemma aux_lemma: "sum_list (filter (\<lambda>x. x<(0::int)) l) + sum_list (filter (\<lambda>x. x>0) l) = sum_list l"
  (* No idea how to prove that right now, but I'm sure it holds, and I need this for further proofs \<dots> *)
  sorry
    
(* Be careful, with sorry Isabelle will accept any nonsense! *)
lemma nonsense: "x>Suc 0 \<Longrightarrow> y>0" sorry

(* And once you have an inconsistency in the system, you can prove everything *)
lemma "True = False" using nonsense[of 2 0] by auto
    
    
    
    
  
  

section \<open>For all elements in list\<close>    
  (* Define a function that checks wether a predicate P holds for all elements in a list.
     Note: A predicate is just a function of type "'a \<Rightarrow> bool". It must evaluate to True for all elements in the list.
  *)
  
  fun listall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
    "listall P [] \<longleftrightarrow> True" (* Return True for the empty list. *)
(*<*)    
  | "listall P (x#xs) \<longleftrightarrow> P x \<and> listall P xs"
(*>*)    
    

  (* Show: P holds for all elements of xs@ys, if and only if it holds for all elements of xs and for all elements of ys: *)  
  lemma "listall P (xs@ys) \<longleftrightarrow> listall P xs \<and> listall P ys"  
(*<*)    
    by (induction xs) auto  
(*>*)    

  (* Show: When checking P for a  mapped list, we can also apply the function before we evaluate P *)    
  lemma "listall P (map f xs) = listall (\<lambda>x. P (f x)) xs"
(*<*)    
    by (induction xs) auto  
(*>*)    
  
  (* Specify and show: If we filter the list with P, all elements in the result will satisfy P.
    Note: In this exercise, you have to come up with both, the formula and the proof!
  *)    
  lemma 
(*<*)    
    "listall P (filter P xs)" 
      by (induction xs) auto
(*>*)    
  
  
section \<open>Sum of elements in a list\<close>  
  
(* Specify a function to sum up all elements in a list of integers. The empty list has sum 0. *)  
  
  fun listsum :: "int list \<Rightarrow> int" where
  (*<*)  
    "listsum [] = 0"
  | "listsum (x#xs) = x + listsum xs"  
  (*>*)
    
  (* Some solutions inserted a superfluous equation here:
  *)  

  fun listsum_complicated :: "int list \<Rightarrow> int" where
    "listsum_complicated [] = 0"
  | "listsum_complicated [x] = x"  
  | "listsum_complicated (x#xs) = x + listsum_complicated xs"  
    
  (* This makes the function unnecessarily complicated, and will cause trouble in the proofs later.

    An important thing to note here:
  *)  
  thm listsum_complicated.simps  
    
  (*
    "listsum_complicated (x#xs) = x + listsum_complicated xs"
    is not a simplification lemma: Prior patterns override later ones, such that
    the third equation is only applied if xs is not empty!

    Sometimes, such cases are not avoidable, then you have to prove the 
    missing lemmas yourself:
  *)  
  lemma [simp]: "listsum_complicated (x#xs) = x + listsum_complicated xs"
    apply (cases xs) apply auto done
    
    
    
    
  
  (* Show the following lemmas: *)

  (* Instead of summing over xs@ys, we can also add the results from summing over xs and summing over ys *)  
  lemma listsum_append: "listsum (xs@ys) = listsum xs + listsum ys"
    (*<*)
    by (induction xs) auto  
    (*>*)  
    
  (* Filtering out zeroes does not affect the sum *)    
  lemma listsum_filter_z: "listsum (filter (op\<noteq>0) l) = listsum l"  
    (*<*)
    by (induction l) auto  
    (*>*)  

  (* Reversing a list does not affect the sum. HINT: You'll need an auxiliary lemma. (that you already have proved) *)
  lemma listsum_rev: "listsum (rev xs) = listsum xs"    
    (*<*)
    apply (induction xs) apply (auto simp: listsum_append)
    done
    (*>*)  
    
  (* Specify and prove: If summing up a list with only non-negative numbers, the result will be non-negative: *)  
      
  lemma "listall (\<lambda>x. 0\<le>x) xs \<Longrightarrow> 0 \<le> listsum xs"
    by (induction xs) auto
    
  (** I saw many wrong solutions here. The two most common mistakes were:

    1. Confusing positive (x>0) with non-negative (x\<ge>0)

    2. Specifying the list that does only contain non-negative numbers by a filter:
  *)    
      
      prop "listsum (filter (\<lambda>x. x\<ge>0) xs) \<ge> 0"
        
  (**
    While this is, intuitively, an equivalent formula, it does not reflect 
    the textual specification precisely. In particular, it is not trivial 
    (although easy) to see that all lists with only non-negative numbers can
    actually be represented by filtering of some list.
  *)      
      
      
      
    
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
    (*<*)
    "denc prv [] = []"
  | "denc prv (x#xs) = (x-prv)#denc x xs"  
    (*>*)
  
  (* Specify the decoder. Again, the first argument represents the previous 
      decoded value, and can be initialized to 0. *)  
  fun ddec :: "int \<Rightarrow> int list \<Rightarrow> int list" where
    (*<*)
    "ddec prv [] = []"
  | "ddec prv (d#ds) = (prv+d) # ddec (prv+d) ds"
    (*>*)
  
  (* Show that encoding and then decoding yields the same list. HINT: The lemma will need generalization. *)  

  (*<*)  
  lemma dec_enc_id_aux: "ddec s (denc s l) = l"
    by (induction l arbitrary: s) auto  
  (*>*)
    
  lemma "ddec 0 (denc 0 l) = l"
  (*<*)  
    by (simp add: dec_enc_id_aux)
  (*>*)
      
      
end
