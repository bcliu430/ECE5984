theory Project
imports IPP_Lib
begin


(** PROJECT ASSIGNMENT FOR CERTIFIED PROGRAMMING COURSE

  ISSUED: Nov 17, 2017
  DUE: Dec 11, 11:59pm, 2017

  The deadline is the same for the graduate and undergraduate section.
  However, graduate students have to solve both, part I and part II, while
  undergraduates only need to solve part I.
*)


chapter \<open>General Hints and Guidelines\<close>
text \<open>
  \<^item> This folder comes with a large collection of 
    examples (@{file \<open>Examples.thy\<close>}), which may provide some reference 
    on how to use the VCG. It is basically the VCG we used in Tutorial5!


  \<^item> For the sorting algorithm, the two parts of its specification, i.e., 
    sortedness and preservation of elements, are independent, and you can prove 
    each part separately! For example, you might first want to only prove 
    preservation, and then extend your invariants and specifications to also
    show sortedness. 
    
    If you managed to prove one property, but not not both, make sure to submit a theory that contains:
      \<^item> A complete theory file with the proof of one property, without any \<open>sorry\<close>s. 
      \<^item> A separate file with your failed proof attempt of the other property or the full 
        specification. 
  
  \<^item> If you should have problems proving total correctness, you may also prove partial correctness!
    However, note that the termination proofs are straightforward!
    
  \<^item> Start working on the project EARLY! You cannot solve this project on 
    the weekend before the deadline!
    
\<close>



chapter \<open>Part I: Insertion Sort\<close>
(* To be solved by all students *)

text \<open>The objective of this project is to develop an insertion sort algorithm.
  See \<^url>\<open>https://en.wikipedia.org/wiki/Insertion_sort\<close> for an overview.
  Parts of this project assignment will refer to the terminology used in 
  the Wikipedia article, so it is highly recommended to read it first!
\<close>


context 
begin

unbundle IMP_Syntax       
interpretation Vcg_Aux_Lemmas .

section \<open>Algorithm\<close>
text \<open>
  We modify the algorithm presented at the Wikipedia page to sort an array \<open>a\<close>
  in the range \<open>l..<h\<close>.
  Recall that our array indexes are integers, so there are no restrictions on
  \<open>l\<close> or \<open>h\<close> being positive (This will make the proofs simpler!).

  We split the algorithm into three parts:
    \<^item> a swap function, which swaps \<open>a[j-1]\<close> and \<open>a[j]\<close>
    \<^item> an insert function, which inserts element a[i] to its correct position 
      in a[l..<i]
    \<^item> the main loop, which sorts the array by repeatedly calling insert.  
    
\<close>

definition "swap_prog \<equiv> CLR t;; t::=a\<^bold>[$j - \<acute>1\<^bold>];; a\<^bold>[$j - \<acute>1\<^bold>]::=a\<^bold>[$j\<^bold>];; a\<^bold>[$j\<^bold>]::=$t"

definition "insert_prog \<equiv>
  CLR j;;
  j::=$i;;
  WHILE $j>$l && a\<^bold>[$j-\<acute>1\<^bold>] > a\<^bold>[$j\<^bold>] DO (
    swap_prog;;
    j::=$j - \<acute>1
  )"

definition "sort_prog \<equiv> 
  CLR i;;
  i::=$l + \<acute>1;;
  WHILE $i < $h DO (
    insert_prog;;
    i::=$i+\<acute>1
  )"

(* Boilerplate to make automatic computation of modified variable's approximation work smoothly *)  
lemma [simp]: "lhs_vars swap_prog = {''a'',''t''}" by (auto simp: swap_prog_def)
lemma [simp]: "lhs_vars insert_prog = {''a'',''t'',''j''}"
  by (auto simp: insert_prog_def)
lemma [simp]: "lhs_vars sort_prog = {''i'', ''a'', ''t'', ''j''}"
  by (auto simp: sort_prog_def)
  
section \<open>Verification\<close>

text \<open>Your task is to verify that this algorithm terminates and actually sorts the array!

  Recall that sorting an array requires to specify that:
    \<^enum> the resulting array is actually sorted, 
    \<^enum> and contains exactly the elements of the original array 
\<close>

subsection \<open>Sorted Range\<close>  

text \<open>Sortedness of a range \<open>l..<h\<close> can be expressed as follows:\<close>
definition ran_sorted :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "ran_sorted a l h \<equiv> \<forall>i\<in>{l..<h}. \<forall>j\<in>{l..<h}. i\<le>j \<longrightarrow> a i \<le> a j"

text \<open>Here, the notation \<open>{l..<h}\<close> denotes the sets of numbers in range \<open>l..<h\<close>,
  and comes with a reasonable setup.
  
  A more primitive way of defining sortedness would be the following:
\<close>  
lemma ran_sorted_alt: "ran_sorted a l h = ( \<forall>i j. l\<le>i \<and> i<j \<and> j<h \<longrightarrow> a i \<le> a j)" 
  by (smt atLeastLessThan_iff ran_sorted_def)
  
text \<open>While working on this project, you are likely to require more
  lemmas about sorted ranges. It is a good idea to put these lemmas here,
  and not intersperse them with the other lemmas of your theory.
\<close>

subsection \<open>Multiset of Range\<close>
text \<open>For the multiset of the elements in a range, we use @{const mset_ran}.
  The lemmas needed for this are provided, you should never need to unfold
  @{thm mset_ran_def}.
\<close>


subsection \<open>Swap\<close>

text \<open>We define a function to swap two elements of a range\<close>
definition "swap a i j \<equiv> a(i:=a j, j:=a i)"

text \<open>And prove that it preserves the multiset of that range\<close>
lemma mset_ran_swap: "\<lbrakk> l\<le>i; i<j; j<h \<rbrakk> 
  \<Longrightarrow> mset_ran (swap a i j) l h = mset_ran a l h"
  by (auto simp: swap_def mset_ran_subst_inside)

text \<open>Remark on variable bindings in pre/postconditions:
  Array variables must be bound as \<open>(name:imap)\<close>! 
  See specification below for an example!
\<close>  

lemma swap_prog_correct[vcg_rules]: "\<Turnstile>\<^sub>t {\<lambda>a\<^sub>0. vars (a:imap) j in a=a\<^sub>0} 
            swap_prog 
          {\<lambda>a\<^sub>0. vars (a:imap) j in a=swap a\<^sub>0 (j-1) j} mod {''a'',''t''}"
  unfolding swap_prog_def (* Note: swap_prog is defined as constant, so you have to unfold its definition! *)
  apply vcg
  by (simp add: Project.swap_def)
    
section \<open>Insert\<close>

text \<open>
  The insert algorithm is the most tricky part! 
  It takes a sorted range \<open>l..<i\<close> and then "swaps down" the
  element \<open>i+1\<close> to its correct position. During the loop,
  \<open>j\<close> is the index of the swapped-down element.
  
  Intuitively, \<open>j\<close> splits the range \<open>l..<i+1\<close> into a left range L=\<open>l..<j\<close> and 
  a right range R=\<open>j+1..<i+1\<close>. The element \<open>j\<close> is in the gap between L and R.
  
  Hint: Drawing this situation on a piece of paper might help a lot in getting the intuition! 

  Initially, the range R is empty. During the loop, the following invariant is maintained:
    \<^item> L and R are both sorted
    \<^item> The elements of L are smaller than or equal than the elements of R
    \<^item> The element a[j] is (strictly) smaller than every element of R
    \<^item> The multiset of the whole array (l..<h) does not change

  When the loop terminates, a[j] is greater than or equal the last element
  of L. Moreover, the invariant guarantees that a[j] is less than the elements 
  in R, and both L and R are sorted. Thus, the whole range \<open>L a[j] R\<close> is sorted.
    
  Note that we phrased some relations on every element of L or R. 
  As L and R are sorted, it might be tempting to say, e.g., 
  
    \<^item> the last element of L is less than or equal than the first element of R
    
  However, L and R may be empty, and thus have no last/first element, 
  which would require to formalize a lot of corner cases. With our 
  formulation, we can just write, e.g., \<open>\<forall>k\<in>{j+1..<i+1}. \<dots>\<close>, regardless 
  of whether the range is empty or not.
  
\<close>

(** Define the invariant and prove the insert algorithm correct! *)
definition insert_invar :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "insert_invar a\<^sub>0 a l h i j \<equiv> 
    i \<ge> j \<and> i> l \<and> h > i \<and> (* boundary conditions*)
    ( \<forall>k\<in>{j+1..<i+1}. a j \<le> a k)\<and> (* a[j] < R *)
    ran_sorted a l j \<and> ran_sorted a (j+1) (i+1) \<and>(* L and R are sorted*)
    (\<forall>k1\<in>{l..<j}. \<forall>k2\<in>{j+1..<i+1}. a k1 \<le> a k2) \<and>  (* Elements of L \<le> R *)
    mset_ran a l h = mset_ran a\<^sub>0 l h   (* Multiset of whole range unchanged *)
    "

subsection \<open>VCs\<close>
(**
  Hint: Extract each verification condition to its own lemmas. 
    To prove these lemmas, more auxiliary lemmas and Isar proofs may be 
    a good idea (although skillful use of auto/sledgehammer may bring you quite far).

    Moreover, it is very likely that quickcheck will find counterexamples 
    to your VCs, if your invariant/spec is wrong. Sometimes, these counterexamples 
    help to fix the invariant/spec. See below for example!
    
    Below are just a few examples of lemmas that I used 
    (For you, they may look different)
*)

subsubsection \<open>Auxiliary Lemmas\<close>
text \<open>Swapping outside a range does not change its sortedness.
  (here the two elements right of the range are swapped) 
\<close>
lemma ran_sorted_swap_outside:
  "ran_sorted (swap a (j - 1) j) l (j - 1) \<longleftrightarrow> ran_sorted a l (j-1)"
  by (auto simp: ran_sorted_def swap_def)

text \<open>
  Swapping and extending R by one element to the left preserves sortedness.
\<close>
lemma  
  "\<lbrakk>l < j;                              (* L not empty, i.e., there is a last element to swap with  *)
    ran_sorted a (j + 1) (i + 1);       (* R is sorted *)
    \<forall>k1\<in>{l..<j}. \<forall>k2\<in>{j + 1..<i + 1}. a k1 \<le> a k2 (* Elements in L \<le> R *)
  \<rbrakk> 
  \<Longrightarrow> ran_sorted (swap a (j - 1) j) j (i + 1)" (* Extended R is sorted after swapping *)
  
  sorry (* You only need to prove this lemma if you actually use it. 
            Otherwise, remove it from your submission. *)
  
(* Add more lemmas here as required *)


  
subsubsection \<open>VCs\<close>
(* Put your lemmas that you extracted from the VCG here *)
lemma ins_aux0: 
"\<And>z a l h i ja k.
       l < ja \<Longrightarrow>
       a ja < a (ja - 1) \<Longrightarrow>
       i < h \<Longrightarrow>
       \<forall>k\<in>{ja + 1..<i + 1}. a ja \<le> a k \<Longrightarrow>
       ran_sorted a l ja \<Longrightarrow>
       ran_sorted a (ja + 1) (i + 1) \<Longrightarrow>
       \<forall>k1\<in>{l..<ja}. \<forall>k2\<in>{ja + 1..<i + 1}. a k1 \<le> a k2 \<Longrightarrow>
       mset_ran a l h = mset_ran z l h \<Longrightarrow> ja \<le> k \<Longrightarrow> k \<le> i \<Longrightarrow> swap a (ja - 1) ja (ja - 1) \<le> swap a (ja - 1) ja k"

  unfolding mset_ran_def swap_def image_mset_def
  by simp
lemma ins_aux1:   " \<And>z a l h i ja.
       l < ja \<Longrightarrow>
       a ja < a (ja - 1) \<Longrightarrow>
       ja \<le> i \<Longrightarrow>
       i < h \<Longrightarrow>
       \<forall>k\<in>{ja + 1..<i + 1}. a ja \<le> a k \<Longrightarrow>
       ran_sorted a l ja \<Longrightarrow>
       ran_sorted a (ja + 1) (i + 1) \<Longrightarrow>
       \<forall>k1\<in>{l..<ja}. \<forall>k2\<in>{ja + 1..<i + 1}. a k1 \<le> a k2 \<Longrightarrow>
       mset_ran a l h = mset_ran z l h \<Longrightarrow> ran_sorted (swap a (ja - 1) ja) ja (i + 1)"
  unfolding mset_ran_def swap_def image_mset_def
  by (simp add: ran_sorted_def)

lemma ins_aux2 :"\<And>z a l h i ja k1 k2.
       a ja < a (ja - 1) \<Longrightarrow>
       i < h \<Longrightarrow>
       \<forall>k\<in>{ja + 1..<i + 1}. a ja \<le> a k \<Longrightarrow>
       ran_sorted a l ja \<Longrightarrow>
       ran_sorted a (ja + 1) (i + 1) \<Longrightarrow>
       \<forall>k1\<in>{l..<ja}. \<forall>k2\<in>{ja + 1..<i + 1}. a k1 \<le> a k2 \<Longrightarrow>
       mset_ran a l h = mset_ran z l h \<Longrightarrow>
       l \<le> k1 \<Longrightarrow> k1 < ja - 1 \<Longrightarrow> ja \<le> k2 \<Longrightarrow> k2 \<le> i \<Longrightarrow> swap a (ja - 1) ja k1 \<le> swap a (ja - 1) ja k2"
  unfolding mset_ran_def swap_def image_mset_def
  by (simp add: ran_sorted_alt)
  
lemma insert_aux0: "\<And>z a l h i ja.
       insert_invar z a l h i ja \<Longrightarrow> l < ja \<Longrightarrow> a ja < a (ja - 1) \<Longrightarrow> insert_invar z (swap a (ja - 1) ja) l h i (ja - 1)"
  apply (auto simp: insert_invar_def)
  prefer 2 
  using ran_sorted_alt ran_sorted_swap_outside apply auto[1]
  prefer 4
  apply (simp add: mset_ran_swap)
  using ins_aux0 apply blast  
  using ins_aux1 apply blast
  using ins_aux2 apply blast
  done

lemma insert_aux1: "\<And>z a l h i j. l < j \<longrightarrow> \<not> a j < a (j - 1) \<Longrightarrow> insert_invar z a l h i j \<Longrightarrow> ran_sorted a l (i + 1)"
  apply (auto simp: insert_invar_def)
  apply (smt atLeastLessThan_iff ran_sorted_alt)
  by (smt atLeastLessThan_iff ran_sorted_alt)
lemma insert_aux2: "\<And>z l i h. l < i \<Longrightarrow> i < h \<Longrightarrow> ran_sorted z l i \<Longrightarrow> insert_invar z z l h i i"
  apply (auto simp: insert_invar_def)
  by (simp add: ran_sorted_alt)

subsection \<open>Correctness Proof\<close>
lemma insert_correct[vcg_rules]: "
  \<Turnstile>\<^sub>t {\<lambda>a\<^sub>0. vars l i h (a:imap) in a=a\<^sub>0 \<and> l<i \<and>i<h \<and> ran_sorted a l i} 
        insert_prog 
     {\<lambda>a\<^sub>0. vars l i h (a:imap) in 
        ran_sorted a l (i+1) 
      \<and> mset_ran a l h = mset_ran a\<^sub>0 l h
      }
     mod {''a'',''t'',''j''}"
  unfolding insert_prog_def
  supply insert_aux0[simp] insert_aux1[simp] insert_aux2[simp]
  apply (rewrite annot_tinvar[where
        R = "measure_exp ($j - $l)" and
        I = "\<lambda>a\<^sub>0. vars (a:imap) l h i j in insert_invar a\<^sub>0 a l h i j" ])
  apply (vcg_all; (auto simp: insert_invar_def; fail)?)
  done

section \<open>Insertion Sort\<close>
  
text \<open> Here, you are on your own! 
  Come up with a specification for @{const sort_prog} and prove it correct.
  
  Note: Do not use @{term lran} as in Tutorial~5, but use 
  our @{const ran_sorted} and @{const mset_ran}! These do not go the detour 
  over lists, and are thus easier to handle!
  
  Note: You are *not* required to specify that the elements 
    of the array outside the range \<open>l..<h\<close> are preserved (cf. Bonus 1).
\<close>

definition sort_invar :: "(int \<Rightarrow> int)\<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "sort_invar a\<^sub>0 a l h i  \<equiv>
  ran_sorted a l i \<and>
  i > l \<and> i \<le> h \<and>
  mset_ran a l h = mset_ran a\<^sub>0 l h 
"

lemma sort_correct[vcg_rules]: "
  \<Turnstile>\<^sub>t {\<lambda>a\<^sub>0. vars l h i (a:imap) in a=a\<^sub>0 \<and> l<h} 
  sort_prog
  {\<lambda>a\<^sub>0. vars l h i (a:imap) in         
      ran_sorted a l h
      \<and> mset_ran a l h = mset_ran a\<^sub>0 l h
  } mod {''a'',''t'', ''i'',''j''}"
  unfolding sort_prog_def
  apply (rewrite annot_tinvar[where
        R="measure_exp ($h - $i)" and
        I="\<lambda>a\<^sub>0. vars (a:imap) l h i in sort_invar a\<^sub>0 a l h i " ])
  apply (vcg_all; (auto simp: sort_invar_def; fail)?)
  by (simp add: ran_sorted_alt sort_invar_def)

  
section \<open>Bonuses\<close>
(* To grab some bonus points, for all students. 

  We give 3 bonus assignments, each worth 5 bonus-% towards your final grade,
  i.e., these will be directly added to your final course percentage, 
  from which your grade will be computed. 

  WARNING: Only attempt these after you have solved the regular project!
    The first bonus assignment is relatively easy, the last two are hard! 
    I will only give points for proofs 
    (or serious proof attempts with partial results), not for
    an implementation of the algorithm without proof!
  
*)

subsection \<open>Elements Outside Range\<close>
text \<open>Augment your specifications and proofs to express that elements outside 
  the range \<open>l..<h\<close> are not touched.
  Hint: @{prop \<open>a = a\<^sub>0 on -{l..<h}\<close>}, @{const eq_on}
\<close>

definition boundary_invar :: "(int \<Rightarrow> int)\<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "boundary_invar a\<^sub>0 a l h i  \<equiv>
ran_sorted a l h\<and>
  i > l \<and> i \<le> h  "

lemma sort_boundary_correct[vcg_rules]: "
  \<Turnstile>\<^sub>t {\<lambda>a\<^sub>0. vars l h i (a:imap) in l<h} 
  sort_prog
  {\<lambda>a\<^sub>0. vars l h i (a:imap) in a = a\<^sub>0 on -{l..<h}
  } mod {''a'',''t'', ''i'',''j''}"
  unfolding sort_prog_def eq_on_def
  apply (rewrite annot_tinvar[where
        R="measure_exp ($h - $i)" and
        I="\<lambda>a\<^sub>0. vars (a:imap) l h i in boundary_invar a\<^sub>0 a l h i " ])
  apply (vcg_all; (auto simp: boundary_invar_def eq_on_def; fail)?)
  prefer 2
  quickcheck
  sorry

subsection \<open>Optimized insert Function\<close>
text \<open>
  The Wikipedia page mentions an optimized version of the inner loop,
  that stores the element at \<open>i\<close>, then shifts the elements of the array to the 
  right while finding the insertion position, and finally inserts the stored element.
  
  Implement and prove (totally) correct the optimized insert function!
  DO NOT CHANGE YOUR ORIGINAL SOLUTION, BUT PROVIDE A COPY OF THE INSERT FUNCTION
\<close>

subsection \<open>Binary Search\<close>
text \<open>
  Implement and prove total correctness of an algorithm to find an index
  \<open>i\<in>{l..<h}\<close> with \<open>a[i] == x\<close>. You may assume that the array is sorted in 
  the range \<open>l..<h\<close>. If the range does not contain the element \<open>x\<close>, return 
  the index \<open>h\<close> (one beyond the end of the range).

  CAVEAT: I will only accept algorithms that run in logarithmic time in 
    the size of the range. The obvious choice is binary search 
    \<^url>\<open>https://en.wikipedia.org/wiki/Binary_search_algorithm\<close>

  HINT: If you plan to solve this bonus, have a look at Part II of the project,
    which is somewhat related!
    
\<close>


chapter \<open>Part II: Sqrt by Bisection\<close>
(* Only GRADUATE students *)

subsection \<open>Bisection\<close>
text \<open>A more efficient way of inverting monotonic functions is by bisection,
  that is, keep track of a possible interval for the solution, and half the 
  interval in each step. The algorithm only needs $O(\log n)$ iterations.
  
  Implement bisection search to determine \<open>\<lfloor>sqrt x\<rfloor>\<close>, i.e., the square root of
  \<open>x\<close>, rounded down. You may assume that \<open>x\<close> is positive!
  
  
  High-level description of the algorithm:
    \<^item> Initialize \<open>l\<close> and \<open>h\<close> with safe under and over approximations, 
      i.e. such that \<open>l\<^sup>2 \<le> x < h\<^sup>2\<close>
  
    \<^item> Iterate: Compute the midpoint \<open>m\<close> of the interval \<open>l..<h\<close>, and check whether 
      \<open>m\<^sup>2 \<le> x\<close>. Depending on this check, adjust \<open>l\<close> or \<open>h\<close>.
      
    \<^item> Terminate the iteration if \<open>l\<close> and \<open>h\<close> are close enough together.
      Hint: You do not need to terminate immediately if you luckily hit
      \<open>m\<^sup>2 = x\<close>, but you can always wait until the interval has shrunk enough.
      This saves you a lot of corner cases and makes the proof simpler.
      
  Warning: Although the final algorithm looks quite simple, 
    getting it right can be quite tricky. It is very prone 
    to off-by-one errors.
    
  Specify the algorithm, and prove total correctness.  
\<close>

definition "sqrt_bisect_prog \<equiv> 
CLR l;; CLR h;;
l::= N 1;;
h::= $x + (N 1);;
WHILE  ($h - $l) > N 1 DO
(
  IF ( (($l + $h) div N 2) *(($l + $h) div N 2) ) <= $x THEN
    l::= (($l + $h) div N 2)
  ELSE
    h::= (($l + $h) div N 2)
)
"

text \<open>Hint: Testing the algorithm before attempting to prove it may be a good idea! \<close>
schematic_goal "(sqrt_bisect_prog, <''x'' := var 1>) \<Rightarrow> ?s"
  unfolding sqrt_bisect_prog_def
  by BigSteps

definition bisection_invar:: " int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
  where "bisection_invar  l h x \<equiv>  1\<le>l \<and> l < h \<and> l\<^sup>2 \<le> x \<and> x < h\<^sup>2"
    
lemma bisect_aux0:    
" \<And>l h x. 1 < h - l \<Longrightarrow>
             bisection_invar l h x \<Longrightarrow> (l + h) div 2 * ((l + h) div 2) \<le> x \<Longrightarrow> bisection_invar ((l + h) div 2) h x"
  apply (auto simp:bisection_invar_def)
  by (simp add: power2_eq_square)
  
lemma bisect_aux1:
"\<And>l h x. 1 < h - l \<Longrightarrow>
             bisection_invar l h x \<Longrightarrow> \<not> (l + h) div 2 * ((l + h) div 2) \<le> x \<Longrightarrow> bisection_invar l ((l + h) div 2) x"
  apply (auto simp:bisection_invar_def)
  by (simp add: power2_eq_square)
  
lemma bisect_aux2:    
" \<And>l h x. \<not> 1 < h - l \<Longrightarrow> bisection_invar l h x \<Longrightarrow> x < (l + 1)\<^sup>2"
  apply (auto simp:bisection_invar_def)
  by smt

lemma bisect_aux3:
" \<And>x. 1 \<le> x \<Longrightarrow> bisection_invar 1 (x + 1) x "
  apply (auto simp:bisection_invar_def)
  by (smt one_less_numeral_iff power_one_right power_strict_increasing semiring_norm(76))
(*
  The specification is provided.
*)  
lemma sqrt_bisect_correct: " 
  \<Turnstile>\<^sub>t {\<lambda>_. vars x in 1\<le>x } 
       sqrt_bisect_prog 
     {\<lambda>_. vars l x in 1\<le>l \<and> l\<^sup>2\<le>x \<and> x<(l+1)\<^sup>2 } mod {''l'',''h'',''m''}"
  unfolding sqrt_bisect_prog_def
  apply (rewrite annot_tinvar[where
        R="measure (\<lambda>s. nat (s ''h'' 0 - s ''l'' 0))" and
        I="\<lambda>_. vars l h x in bisection_invar l h x" 
         ])
  supply bisect_aux0[simp] bisect_aux1[simp] bisect_aux2[simp] bisect_aux3[simp]
  apply (vcg_all; (auto simp: bisection_invar_def; fail)?)
  done
  (*
    Hint: I used the invariant  
      \<open>\<lambda>_. vars l h x in 0\<le>l \<and> l<h \<and> l\<^sup>2\<le>x \<and> x<h\<^sup>2\<close>
    which just states that the solution is in the interval \<open>l..<h\<close>.
  
    Note that, if you implement the algorithm differently than I did, 
    you may need to change the invariant. DO NOT CHANGE THE SPECIFICATION.
  *)  
  
end
end
