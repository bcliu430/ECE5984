theory Tutorial1
imports Main
begin


section \<open>Exists in list\<close>
  (*
    Specify a function "listex P xs" that returns true if xs contains an element
    that satisfies "P". (I.e., if the list xs contains an element x such 
    that "P x" is True)
  *)
  fun listex :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
    "listex P [] = False"
  | "listex P (x#xs) \<longleftrightarrow> P x \<or> listex P xs"  

    
  (* Show: The list xs@ys contains an element that satisfies P, if and only if xs or ys contain such an element *)  
  lemma "listex P (xs@ys) \<longleftrightarrow> listex P xs \<or> listex P ys" 
    apply (induction xs)
     apply auto  
    done  

      
section \<open>Minimum element in list\<close>  

  (* Define a function that returns true if a list contains a specified element.
    Hint: Use listex! *)  
  definition contains :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where 
    "contains x xs = listex (\<lambda>y. y=x) xs"
    (* Replace by your definition *)
  
  (* Specify a function that returns the minimum element of a list of integers.
    Explicitly define your function to be "undefined" for the empty list
    *)
      
  fun minlist :: "int list \<Rightarrow> int" where
    "minlist [] = undefined"
  | "minlist [x] = x"  
  | "minlist (x#xs) = (min x (minlist xs))"  
    (* Add other equations here *)
    
  (* Hint: If you used "let" in your specification, you want to inline 
    it in your proofs by "simp add: Let_def".
 
    Similar, if you used the standard library function "min", you probably want 
    to inline it by "simp add: min_def"
  *)
    

  (* Show: the minimum element is smaller than any element contained in the list *)
lemma "\<lbrakk> contains x l \<rbrakk> \<Longrightarrow> minlist l \<le> x" 
  apply (induction l rule: minlist.induct)
    apply (auto simp: contains_def)
    done

  (* Specify and show: The minimum element 
    of a non-empty list is contained in the list.
    Note: You are required to come up with the formula yourself, and then prove it
  *)    
lemma "l\<noteq>[] \<Longrightarrow> contains (minlist l) l" 
  apply (induction l rule: minlist.induct)
    apply (auto simp: contains_def min_def)  
  done  

  (* Specify and show: If there exists a negative element in the list,
    the minimum element of the list is negative
    *)
  lemma "listex (\<lambda>x. x<0) l \<Longrightarrow> minlist l < 0"
  apply (induction l rule: minlist.induct)
    apply (auto)  
    done      

section \<open>Run-Length encoding\<close>      
  (* Only if some time remains *)
      
  (* The idea of run-length encoding is to replace a "run" of the same symbol
    by its length and one copy of the symbol. For example, the string
    "aaaabbcddddeffff" may be encoded as 4a2b1c4d1e4f. 

    Background: This is a lossless compression algorithm which is most 
      effective on artificially generated images, eg, screenshots. 
      Look at your screen and estimate how many (long) runs of same-coloured 
      pixels you have! For example, the only compression scheme supported 
      by the (now historic) PCX image file format was run-length encoding.
  *)
  
  (* We describe coded words as pairs of a natural number and a symbol 
      value of any type. ('a) *)
  
  type_synonym 'a rle = "nat\<times>'a"
  
  
  (* Model a function rlenc_aux, which takes as first arguments the 
    current multiplicity and the current symbol, and then the remaining 
    symbols to be encoded. 

    ASSUME that the current multiplicity is always 
    positive, i.e., make no special cases for current multiplicity to be
    zero. This means, we can only encode non-empty lists, but will make the 
    proofs simpler. We will add the special case for empty lists later.
  *)  
    
  fun rlenc_aux :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a rle list" where
    "rlenc_aux n a [] = [(n, a)]"
  | "rlenc_aux n a (x#xs) = (if a=x then rlenc_aux (Suc n) a xs else (n,a) # rlenc_aux 1 x xs)"  
    
  (* Test cases *)  
  value "rlenc_aux 3 CHR ''a'' [] = [(3,CHR ''a'')]"  
    (* Already read a run of 3 'a's, nothing more to encode *)
  
  value "rlenc_aux 3 CHR ''a'' ''aabbbeff'' 
    = [(5,CHR ''a''), (3,CHR ''b''), (1,CHR ''e''), (2,CHR ''f'')]"  
    (* Already read 3 'a's, yet have to encode the string 'aabbbeff' *)
    
  (* Recall: A string is just a char list *)
  term "''aaabbbccc''"
    
  (* Extending your function to also cover the empty list is then easy: *)    
  definition rlenc :: "'a list \<Rightarrow> 'a rle list" where
    "rlenc l = (case l of [] \<Rightarrow> [] | x#xs \<Rightarrow> rlenc_aux 1 x xs)"
    
  (* Write a decoder function. 
    Hint: You do not need any assumptions on counts being non-zero. 
    Use the standard-library function "replicate".
  *)  
  term replicate  
  
  fun rldec :: "'a rle list \<Rightarrow> 'a list" where
    "rldec [] = []"
  | "rldec ((n,a) # xs) = replicate n a @ rldec xs"  
  
  value "rldec [] = []"
  value "rldec [(7,CHR ''a''), (1,CHR ''b'')] = ''aaaaaaab''"
    
  (* Prove that encoding and then decoding yields the same list.
    HINT: You will need to generalize the lemma to the form: 
      "rldec (rlenc_aux n a xs) = \<dots>"
 
  *)  
    
  lemma rl_dec_enc_aux[simp]: "rldec (rlenc_aux n a xs) = replicate n a @ xs"
    apply (induction n a xs rule: rlenc_aux.induct)
    apply (auto simp: replicate_append_same)  
    done  
    
  lemma "rldec (rlenc xs) = xs"
    by (auto simp: rlenc_def split: list.split)
  

end
