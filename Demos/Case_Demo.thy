theory Case_Demo
imports Main
begin

lemma "x=5 \<Longrightarrow> x#xs = 5#xs" by auto
    
lemma "x#xs = y#ys"
  apply auto
  oops  
  
lemma "x#ys \<noteq> []" 
  by auto   
  
lemma "(676478456242734::nat) \<noteq> 0" by auto 
  
  
  
  
  
  
  
  
  
  (* Simple case expressions *)
  term "case l of [] \<Rightarrow> 0 | x#xs \<Rightarrow> x + length xs"
  term "case n of 0 \<Rightarrow> 0 | Suc _ \<Rightarrow> 1" (* Wildcards may be used *)
    
  term "case l of [] \<Rightarrow> 0 | _ \<Rightarrow> 1" (* Wildcard will match any remaining patterns *)

  term "case s of [] \<Rightarrow> 1 | [x,y] \<Rightarrow> x+y | _ \<Rightarrow> 0" 
    (* Also complex patterns possible. However, they are translated to 
        sequential patterns on parsing. See output.*) 
    
  (* The full adder by case, with tuples *)  
    
  definition fa :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<times> bool" where
    "fa a b c = ( case (a,b,c) of
      (False, False, False) \<Rightarrow> (False, False)
    | (False, False, True ) \<Rightarrow> (True , False)
    | (False, True , False) \<Rightarrow> (True , False)
    | (False, True , True ) \<Rightarrow> (False, True )
    | (True , False, False) \<Rightarrow> (True , False)
    | (True , False, True ) \<Rightarrow> (False, True )
    | (True , True , False) \<Rightarrow> (False, True )
    | (True , True , True ) \<Rightarrow> (True , True )
    )"
    
  fun to_nat :: "bool list \<Rightarrow> nat" where
    "to_nat [] = 0"
  | "to_nat (x#xs) = (if x then 1 else 0) + 2*to_nat xs"
    
  fun addc :: "bool list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> bool list" where
    "addc [] [] c = (if c then [True] else [])"
  | "addc [] (b#bs) c = (case fa False b c of (s,c) \<Rightarrow> s#addc [] bs c)"  
  | "addc (a#as) [] c = (case fa a False c of (s,c) \<Rightarrow> s#addc as [] c)"  
  | "addc (a#as) (b#bs) c = (case fa a b c of (s,c) \<Rightarrow> s#addc as bs c)"  
  
    
    
  (* Proof: Induction on structure of addc function, using fastforce to automatically discharge goals. auto doesn't work here. 
    Details: Later
  *)  
  lemma "to_nat (addc as bs c) = (to_nat as + to_nat bs + (if c then 1 else 0))"
    apply (induction as bs c rule: addc.induct)
    apply simp  
    apply (fastforce simp: fa_def)
    apply (fastforce simp: fa_def)
    apply (fastforce simp: fa_def)
    done

      
fun odd where
  "odd 0 = False"
| "odd (Suc n) = (n mod 2 = 0)"  
      
definition odd' :: "nat \<Rightarrow> bool" where "odd' n = (n mod 2 = 1)"
  
(*
fun f :: "nat \<Rightarrow> nat" where "f n = f n + 1"  
*)  
  
end
