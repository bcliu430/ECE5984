(* Header of theory always looks like this: *)
theory FunProg_Demo (* Theory name, must coincide with filename *)
imports Main "~~/src/HOL/Library/Multiset" (* List of imported theories. Typically only Main. *)
begin

  section \<open>Datatype Examples\<close> (* Section commands have no semantic meaning, only for source structuring. *)
    (* Hint: Use sidekick-panel! *)
    
  (* First Example: Nat  *)
  (* Data represented as algebraic datatypes: *)
  datatype my_nat = Z | S my_nat 
  (* Intuitive reading: A natural number is either *Z*ero, or the *S*uccessor of a natural number *)
    
  (* Note: Unary representation. 
    Not efficient for computation. But very efficient for proving!
  *)

  (* Use the term command to display a term and its type in the Output panel *)
  term "Z" (* In theory text, terms and types always enclosed in "quotes". *)
  term "''This is a string''" (* Do not confuse with strings *)
  term "CHR ''a''" (* Syntax for single character *) 
    
  term "S Z" (* Function application is written: f x\<^sub>1 ... x\<^sub>n *)
  term "S (S (S Z))" (* Note the parentheses! *)

  term "Z"  
    
  term \<open>S (S Z)\<close> (* You may also use cartouches \<open>...\<close>  instead of quotes. 
      Type backtick ` and wait for completion menu. 
      Hint: Set Plugins>Plugin Options>Isabelle>General>Completion Delay to 0 for smoother typing.
    *)
  (* Hint: Use the Symbols-panel to explore available 
    symbols, and methods how to enter them! *)
    
  datatype 'a my_list = NIL | CONS 'a "'a my_list"
  (* \<open>\<open>'a\<close> is type parameter. May be filled with any type, e.g.: *)
  typ "my_nat my_list" typ "bool my_list"
    
  datatype bintree = Leaf | Node bintree bintree
    
  datatype 'a bt = Leaf' | Node' 'a "'a bt" "'a bt" 
    
  section \<open>Functions\<close>
    
  (* Functions: Recursive functions. For example: *)
  fun add where
    "add Z m = m"
  | "add (S n) m = S (add n m)"

  (* Note: This definition is much simpler than it would be for binary numbers! *)
  (* Also simpler than what you would write in C++ or Java! *)
    
  value "add (S Z) (S (S Z))" (* Evaluate a term *)
  value "add (S n) (S (S (Z)))" (* Partial evaluation also possible! *)
  
  fun appnd  
    where  
    "appnd NIL l = l"
  | "appnd (CONS x l) ll = CONS x (appnd l ll)"  

    
  value "appnd (CONS a (CONS b NIL)) (CONS c (CONS d NIL))"  
    
  (*
      appnd (CONS a (CONS b NIL)) (CONS c (CONS d NIL)) 
    = CONS a (appnd (CONS b NIL) (CONS c (CONS d NIL)))
    = CONS a (CONS b (appnd NIL (CONS c (CONS d NIL))))
    = CONS a (CONS b (CONS c (CONS d NIL)))




    More examples how evaluation works: [DO ON DOC-CAM IF POSSIBLE]

      add (S (S Z)) (S Z)    -- Match with equation add (S n) m = S (add n m)
    = S (add (S Z) (S Z))    -- Match with equation add (S n) m = S (add n m)
    = S (S (add Z (S Z)))    -- Match with equation add Z m = m
    = S (S (S Z))            -- No more equations to match with


  *)  
    
    
    
    
  section \<open>Types\<close>
  (* Every term in Isabelle must be typeable, e.g., it has a type. *)
  term "Z" 
  term "S Z"  
    
    
  term "S" (* Function type indicated by \<Rightarrow>  *)
  term "add" (* Function with many arguments. Note: \<Rightarrow> is right associative, i.e. "a\<Rightarrow>b\<Rightarrow>c" is same as "a\<Rightarrow>(b\<Rightarrow>c)" *)
  term "add (S Z) (S Z)"
  term "add (S Z)" (* Partial application *)
    
  (*
    Hint: press Ctrl (Mac: Cmd) and move the mouse over (almost) any item in the editor window.
      A tooltip will show further information. Left-click will move to the definition of the item.
  *)  
    
    
  (* We may specify type with function definition. If no type specified,
    Isabelle infers most generic one (type inference). *)
  fun numnodes :: "bintree \<Rightarrow> my_nat" where
    "numnodes Leaf = Z"
  | "numnodes (Node t1 t2) = S (add (numnodes t1) (numnodes t2))"  
    
  value "numnodes (Node (Node Leaf Leaf) (Node Leaf (Node Leaf Leaf)))"
    
    
  (* Type annotations may be added everywhere in term. 
    To influence (restrict) inferred type *)
  term "CONS x xs"
  term "(CONS :: my_nat \<Rightarrow> my_nat my_list \<Rightarrow> my_nat my_list) (x::my_nat) xs"
  term "(CONS x xs)::my_nat my_list"  
    
    
  (* Note: Variables and constants are displayed in different color! Useful to find typos! *)  
    
  term "CONS x xs"  
  term "C0NS x xs"
    
  (* Also, bound variables get different color. Bound variable: 
    Occurs in pattern on left hand side of function equation
  *)  
  fun double :: "my_nat \<Rightarrow> my_nat" where
    "double Z = Z"
  | "double (S n) = S (S (double n))"
    
  (* Don't get confused: The function that is actually being defined is rendered
    as a free variable!
  *)  
  term double  (* It only becomes a constant after definition *)
    
  section \<open>Standard Library\<close>  

  (* Of course, Isabelle has data types for natural numbers and lists in
        its standard library. Included by default! With many functions! *)
    
  typ nat
  term "42::nat"  
  term "0::nat" 
  term Suc 

  typ "int"
  term "42::int"
  term "-42::int"
    
  term Suc  
  (* Note: For numerals, you always have to specify the type *)  
  term "Suc 41" (* Unless clear from type inference! *)
  term "(10::int) - 7"  
    
  term "2+3"  
    
  typ bool  
  term True term False

  typ "'a\<times>'b"  
  term "(True, False)"  
  term "(10::nat, True, 5::int, 6::int)"  
  term "(10::nat, (True, (5::int, 6::int)))"  
    
  term fst term snd 
  value "fst (snd (10::nat, True, 5::int, 6::int))"    
      
    
  typ "'a list"  
  term Nil term Cons  
  term "[]" (* Nil *)
  term "x#l" (* Cons *)
  term "[a,b,c]" (* Syntax sugar for a#b#c#Nil *)
  term "l1@l2" (* append *)
    
  term "l1@l2#x1#x2@l3"  
    
  (* Arithmetic operations overloaded for int and nat *)
  value "(3::int) + 7"  
  value "(3::nat) + 7"  
    
  value "(1::int)*3 - 4*5 + 2*6^2" (* Priority and associativity of standard operators is as expected *)

  lemma "x\<ge>y \<Longrightarrow> (x::nat) - y + y = x"  oops
    
  (* BEWARE: Subtraction on nat saturates at 0 *)
  value "(5::nat) - 10"  

  (* BEWARE: Division on int rounds down. In many PLs (such as C), it rounds towards zero! *)
  value "(-3::int) div 2"  
    
  (* Numbers in Isabelle are arbitrary precision! *)
  term "3871637126732613123526352635726456213527813658125817512332323232323::nat"  
  (* Warning: Computing with this may be really slow! 
    But Isabelle's main purpose is proving, not computing. *)
    
  value "(100::nat) + 1" (* A standard machine should take a few seconds for numbers around 1000..2000 here! *)   

  lemma "(3871637126732613123526352635726456213527813658125817512332323232323::nat) > 0" by simp
    (* However, Isabelle proves this (obvious) lemma within a few milliseconds! 
      Note: Proving lemmas will be introduced later!
    *)  

  value "
       (77777777777777777777777777777777777777777777777777777::int) 
      + 22222222222222222222222222222222222222222222222222222"    
    (* It's much better for integers (they use binary representation internally), but still not super-fast! *)
    
  subsection \<open>Boolean Connectives\<close>  
    
  term "a\<and>b \<or> c\<and>\<not>d    \<longrightarrow>    e"  (* Priority is as expected. Use symbols panel to find out how to type these symbols! *)

  (* Don't use *)  
  term "a & b | c & ~d"  
    
  (*
    Priority, from highest to lowest
      \<not>             not
      \<and>             and
      \<or>             or
      \<longrightarrow>, \<longleftrightarrow>      implies, equal
  *)  

  (* Beware of using = for Booleans. It binds stronger than \<and>.  *)  
  value \<open> let A=True; B=False in (A = B)  =  A\<and>B \<or> \<not>A\<and>\<not>B \<close>
    (* This should output True, shouldn't it? *)
    
    (* Actually, it means: *)
    declare [[show_brackets]]
    term "(A = B)  =  A\<and>B \<or> \<not>A\<and>\<not>B"
    declare [[show_brackets = false]] (* To not see all these brackets in the following *)
    
    (* However, we meant *)  
    term "A = B \<longleftrightarrow> A\<and>B \<or> \<not>A\<and>\<not>B"
      
  (* Usually, this is encountered on function definitions: *)
  fun is_a_bit_smaller :: "int \<Rightarrow> int \<Rightarrow> bool" where 
    "is_a_bit_smaller a b \<longleftrightarrow> a < b \<and> b-a < 10"
    
      
  subsection \<open>Some Simple Examples\<close>  
  fun nth_odd :: "nat \<Rightarrow> nat" where
    "nth_odd 0 = 1"
  | "nth_odd (Suc n) = nth_odd n + 2"

  value "int (nth_odd 2)"  

  (* YOU! Define nth_even! *)  
  fun nth_even :: "nat \<Rightarrow> nat" where
    "nth_even 0 = 0"
  | "nth_even (Suc n) = nth_even n + 2"
    
  value "int (nth_even 4)"  
    
    
  (* n\<^sup>2 can be computed as the sum of the first n odd numbers! *)  
  fun square :: "nat \<Rightarrow> nat" where
    "square 0 = 0"
  | "square (Suc n) = nth_odd n + square n"  

  value "square 2"
  value "int (square 5)" (* Using conversion to int for more readable output *)
    
  (* YOU: Define function sum :: nat list \<Rightarrow> nat that sums up the elements of a list.
    E.g. sum [3,4,5] = 12 *)
    
  fun sum :: "nat list \<Rightarrow> nat" where
    "sum [] = 0"
  | "sum (x#xs) = x + sum xs"  
    
  value "int (sum [3,4,5])"  

  (* YOU: Define Fibonacchi sequence: fib :: "nat \<Rightarrow> nat" where
    fib 0 = 0, fib 1 = 1, fib n = fib (n-2) + fib (n-1)
  *)  

  (* YOU: Define function rep_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
    such that "rep_list n l = l @ \<dots> @ l  (n times)"
  *)  
    
  fun rep_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "rep_list 0 l = []"
  | "rep_list (Suc n) l = l @ rep_list n l"  
    
  value "rep_list 5 ''Hello World!''" (* Note: Strings are just lists of characters! *) 
  typ string
  
    
    
    
  subsection \<open>Some list functions\<close>
  
  subsubsection \<open>Map\<close>  
    
  term map  
  value "map (\<lambda>x. x+1) [-1,-2,3,4,5::int]"
  (* Apply function to each element in list *)
  (* \<open>\<lambda>\<close> used to create ''anonymous'' function. *)
  term "\<lambda>x y z. Suc (x+y+z)" -- \<open>Multiple arguments\<close>  

  (* In Isabelle/HOL, there are no side effects! A term's value will never 
    change as the result of evaluating a term!
  *)
  value "let l=[1,2,3::int] in map (\<lambda>x. x+1) l @ map (\<lambda>x. x+1) l"

    
  subsubsection \<open>Filter\<close>  
  
  definition "f x = (x>0)"  
  value "filter f [-3,-6,3,4,-5,9::int]"
    
  value "filter (\<lambda>x. x>0) [-3,-6,3,4,-5,9::int]"
  (* Filter out elements that do not satisfy condition *)

  section \<open>Quicksort\<close>  
    
  (* We select the first element as pivot.
    Note: Simpler than imperative in-situ implementation, as
      no swapping of array elements is required.
      However: Also less efficient :( But same worst and average case complexity!
  *)
    
  fun qsort :: "int list \<Rightarrow> int list" where
    "qsort [] = []"
  | "qsort (p#xs) = qsort (filter (\<lambda>x. x\<le>p) xs) @ p # qsort (filter (\<lambda>x. x>p) xs)"  
    
  value "qsort [3,4,1,7,8,4]"    

  subsection \<open>Outlook: Correctness proof\<close>  
    
  (* Let's prove that quicksort actually sorts the list.
    We have to show:
      \<^enum> The elements and the number of each element is not altered by sorting
      \<^enum> The resulting list is sorted
  *)

  (* We show that the multiset of the result list is the same 
    as the multiset of the original list.

    Multiset (sometimes called bag): Elements with counts, but no order.
  *)
  lemma qsort_pres_mset: "mset (qsort xs) = mset xs"
    apply (induction xs rule: qsort.induct) 
    using mset_compl_union[where P="\<lambda>x::int. x\<le>p" for p, unfolded not_le]
    by auto

  (* We use the predicate sorted from the standard library 
    to express sortedness of a list:
  *)
  lemma qsort_sorted: "sorted (qsort xs)"
    by (induction xs rule: qsort.induct)
       (auto simp: sorted_append sorted_Cons mset_eq_setD[OF qsort_pres_mset])
       
  (*For now, just ignore the proofs. After the Isabelle introduction, you'll 
    be able to conduct similar proofs easily!*)

    
end
