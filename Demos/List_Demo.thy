theory List_Demo
imports Main
begin

  
datatype 'a list = Nil | Cons "'a" "'a list"

datatype 'a ll = Nil | Cons "'a * 'a" "'a ll"  
  
datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"
  
term "Nil"

declare [[names_short]]

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

(* Associativity of append. 
  Intuitively: It makes no difference if we first append xs and ys, 
  and then append zs to the result, or if we first append ys and zs, 
  and append the result to xs.
*)
lemma "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply auto
  done  

(*
  Reverse a list ... we'll come here later!
*)
fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev(Cons True (Cons False Nil))"

value "rev(Cons a (Cons b Nil))"

theorem rev_rev: "rev (rev xs) = xs"
apply (induction xs)
apply (auto)
(* For now, we are stuck here: We'll later see how to complete the proof. *)    
oops (* Oops cancels unsuccessful proof attempt. *)


end
