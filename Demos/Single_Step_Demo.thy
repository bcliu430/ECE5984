theory Single_Step_Demo
imports Main
begin

text{* "thm" is a command that displays one or more named theorems: *}
thm conjI impI iffI notI

text{* Instantiation of theorems: "of" *}

text{* Positional: *}
thm conjI[of "A" "B"]
thm conjI[of "A"]
thm conjI[of _ "B"]

text{* By name: *}
thm conjI[where ?Q = "B"]
thm conjI[where Q = "B"]   (* May omit ? *)
  
(* If variable name ends with number, ? and ".0" must be written! (Idiosyncrasy of Isabelle) *)
lemma my_rev_append: "rev (a1@a2) = rev a2 @ rev a1" by (rule rev_append)
thm my_rev_append    
thm my_rev_append[where ?a1.0 = "[]"]
    
  

text{* Composition of theorems: OF *}

thm refl[of "a"]
thm conjI[OF refl[of "a"] refl[of "b"]]
thm conjI[OF refl[of "a"]]
thm conjI[OF _ refl[of "b"]]

text{* A simple backward proof: *}
lemma "\<lbrakk> A; B \<rbrakk> \<Longrightarrow> A \<and> B"
apply(rule conjI)
apply assumption
apply assumption
done

end
