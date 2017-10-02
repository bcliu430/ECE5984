theory Simp_Demo
imports Complex_Main
begin

section{* How to simplify *}

text{* No assumption: *}
lemma "ys @ [] = []"
apply(simp)
oops (* abandon proof *)

text{* Simplification in assumption: *}
lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs"
apply(simp)
done

text{* Using additional rules: *}
lemma "(a+b)*(a-b) = a*a - b*(b::int)"
apply(simp add: algebra_simps)
done

text{* Giving a lemma the simp-attribute: *}
declare sorted_Cons [simp]


subsection{* Rewriting with definitions *}

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n*n"

lemma "sq(n*n) = sq(n)*sq(n)"
apply(simp add: sq_def) --"Definition of function is implicitly called f_def"
done

subsection{* Case distinctions *}

text{* Automatic: *}
lemma "(A & B) = (if A then B else False)"
apply(simp)
done

lemma "if A then B else C"
apply(auto)
oops

text{* By hand (for case): *}
lemma "1 \<le> (case ns of [] \<Rightarrow> 1 | n#_ \<Rightarrow> Suc n)"
apply(simp split: list.split)
done

text \<open>By hand: if in assumptions\<close>  
lemma "\<lbrakk> if b then x>(0::nat) else x>2 \<rbrakk> \<Longrightarrow> x*x > 0"
  apply (simp split: if_split_asm)
  done  
  
text \<open>By hand: case in assumptions\<close>
lemma "\<lbrakk> case xs of [] \<Rightarrow> ys\<noteq>[] | _ \<Rightarrow> length xs < length ys \<rbrakk> \<Longrightarrow> length xs < length ys"  
  apply (simp split: list.split_asm)
  done  
    
(* XXX.splits = XXX.split XXX.split_asm. If no further control of splitting required, use XXX.splits. *)    
    
lemma "\<lbrakk> case xs of [] \<Rightarrow> ys\<noteq>[] | _ \<Rightarrow> length xs < length ys \<rbrakk> \<Longrightarrow> length xs < length ys"  
  apply (simp split: list.splits)
  done  
    
    
  
subsection {* Arithmetic *}

text{* A bit of linear arithmetic (no multiplication) is automatic: *}
lemma "\<lbrakk> (x::nat) \<le> y+z;  z+x < y \<rbrakk> \<Longrightarrow> x < y"
apply(simp)
done

lemma "(a+b)*(a-b) = a*a - b*(b::int)"
apply(simp add: algebra_simps) (* More arithmetic rules *)
done
  
lemma "(a/b::real) ^ 5 = (a^5)/(b^5)"
  by (simp add: field_simps) (* Even more rules, in particular about / on fields (eg real)*)
  

subsection{* Tracing: *}

lemma "rev[x] = []"
supply [[simp_trace]] apply(simp)
oops

text{* Method ``auto'' can be modified almost like ``simp'': instead of
``add'' use ``simp add'': *}

end
