theory Induction_Demo
imports Main
begin

subsection{* Generalization *}  
  
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

value "itrev [1,2,3::int] [6,7,8]"

lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
   apply (auto)  
   done 
    
lemma itrev_rev_aux: "itrev xs ys = rev xs @ ys"
  apply (induction xs ys rule: itrev.induct)
   apply (auto)  
   done 


lemma "itrev xs [] = rev xs"
  by (auto simp: itrev_rev_aux)


subsection{* Computation Induction *}

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a [] = []" |
"sep a [x] = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"

lemma "map f (sep a xs) = sep (f a) (map f xs)"
apply(induction a xs rule: sep.induct)
apply auto
done

subsection {* Auxiliary Lemmas *}  
  
hide_const rev  (* Get predefined rev of standard lib out of way! *)  
fun rev where 
  "rev [] = []"  
| "rev (x#xs) = rev xs @ [x]"  
  
lemma "rev (xs @ [a]) = a # rev xs"  
  apply (induction xs) apply auto done

lemma [simp]: "rev (xs @ ys) = rev ys @ rev xs"  
  apply (induction xs) apply auto done
    
    
lemma "rev (rev xs) = xs"  
  apply (induction xs)
   apply auto  
  done  
  (* oops ( We get stuck here! Auxiliary lemma needed! *)  
  
  
end
