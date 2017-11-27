theory Homework6_1
imports "../IMP/Big_Step"
begin

  (*
    ISSUED: Wednesday, October 25
    DUE: Wednesday, November 1, 11:59pm
    POINTS: 5
  *)


section \<open>Derivation Trees\<close>

(*
  Consider the following program, that will compute 
  1+...+n, and return the result in a
*)

abbreviation (input) w where "w\<equiv>    
  WHILE Less (N 0) (V ''n'') DO (
    ''a'' ::= Plus (V ''a'') (V ''n'');;
    ''n'' ::= Plus (V ''n'') (N (-1))
  )
"

abbreviation (input) "gauss \<equiv>
  ''a'' ::= N 0;;
  w
"

(*
  Do a forward derivation of a big-step execution,
  for program gauss and start state <''n'':=2>
*)


lemmas fwd_gauss = Seq[where c\<^sub>1="''a'' ::= N 0" and c\<^sub>2=w and s\<^sub>1="<''n'':=2>", OF
  Assign
  _ (* Insert rest of derivation tree here! *),
  simplified
]

(* Test: Your lemma should solve the following goal: *)
schematic_goal "(gauss,<''n'':=2>) \<Rightarrow> ?s"
  apply (rule fwd_gauss)
  done oops

(* Do a backward derivation. Do not use BigSteps, nor the fwd_gauss rule, 
    but apply only 
      rule Seq, rule Assign, rule WhileTrue, rule WhileFalse, and simp!
*)  
schematic_goal "(gauss,<''n'':=2>) \<Rightarrow> ?s"
  apply (rule Seq)
   apply (rule Assign)
  apply simp
  oops (* Finish the backwards derivation! *)

section \<open>Quotient, Rounded Down\<close>
  
(* Write a program that returns the quotient, rounded down, of two positive 
  numbers x and y, in variable q.
  
  Note: Due to the limited operations available, in particular no Minus,
    finding the simplest program may require a little thought. You may need an auxiliary variable.
  Hint: You only need a single WHILE loop, and no IF.
  Hint: It might be a good idea to sketch the program in pseudocode or C first,
    before you write it down in IMP syntax.
  
*)

abbreviation "IMP_div \<equiv> SKIP" (* Replace by your program! *)

(* Test your program for different test cases!
  In particular, make sure that rounding down is correct, e.g.,
    5 div 3 = 1
    6 div 3 = 2
    7 div 3 = 2

*)
schematic_goal [simplified]: "(IMP_div,<''x'' := 3, ''y'' := 2>) \<Rightarrow> ?s"
  by BigSteps 
  
end
