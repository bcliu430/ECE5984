theory Tutorial2_2
imports Main
begin

  section \<open>Arithmetic Expressions with Exceptions\<close>
    
  text \<open>Model arithmetic expressions that have constants, variables, plus, and div.\<close>  
    
  type_synonym vname = string
  type_synonym val = int
  type_synonym state = "vname \<Rightarrow> val"
  
  datatype aexp = N int | V vname | Plus aexp aexp | Div aexp aexp

  text \<open>Model the evaluation to return \<open>None\<close> if a division by zero occurs, and \<open>Some v\<close> otherwise.
    Use case distinctions to distinguish between None and Some results.
  \<close>  

  fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val option" where
    "aval (N i) s = Some i"
  | "aval (V x) s = Some (s x)"
  | "aval (Plus a1 a2) s = (case aval a1 s of
      None \<Rightarrow> None
    | Some v1 \<Rightarrow> (case aval a2 s of
        None \<Rightarrow> None
      | Some v2 \<Rightarrow> Some (v1+v2)
      )
    )"  
  | "aval (Div a1 a2) s = (case aval a1 s of
      None \<Rightarrow> None
    | Some v1 \<Rightarrow> (case aval a2 s of
        None \<Rightarrow> None
      | Some v2 \<Rightarrow> (if v2=0 then None else Some (v1 div v2))
      )
    )"  
    
text {* A little syntax magic to write larger states compactly: *}

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

  
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

text \<open>Add constant folding to divisions. Consider division of two constants and division by one.
  Be careful not to accidentally "define" division by zero to be \<open>x div 0\<close>.
\<close>

fun division :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "division (N i1) (N i2) = (if i2\<noteq>0 then N (i1 div i2) else Div (N i1) (N i2))"
| "division a (N i) = (if i=1 then a else Div a (N i))"
| "division a b = Div a b"  
 

lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval (Plus a1 a2) s"
apply(induction a1 a2 rule: plus.induct)
apply (auto split: option.splits)
done

lemma aval_div[simp]:
  "aval (division a1 a2) s = aval (Div a1 a2) s"
  apply (induction a1 a2 rule: division.induct)
  apply (auto split: option.splits)  
  done  
  
  
fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
"asimp (Div a\<^sub>1 a\<^sub>2) = division (asimp a\<^sub>1) (asimp a\<^sub>2)"
(* Add an equation for division *)

(* Show correctness of constant folding. *)
theorem aval_asimp[simp]: "aval (asimp a) s = aval a s" 
  apply (induction a)
  apply (auto split: option.splits)  
  done  

end
