theory Tutorial2_1
imports Main
begin

  section \<open>Arithmetic expressions with side-effects\<close>
    
  text \<open>Model arithmetic expressions with an assignment operator 
    \<open>x:=a\<close>, which assigns the result of \<open>a\<close> to variable \<open>x\<close>, and also 
    evaluates to this result. Actually, C and C++ have such assignment 
    operators.

    y = (x=(z=5)) + 6

  \<close>  
    
  text \<open>Start over with the syntax tree\<close>  
  type_synonym vname = string
  type_synonym val = int
  type_synonym state = "vname \<Rightarrow> val"
  
  text {* A little syntax magic to write larger states compactly: *}
  
  definition null_state ("<>") where
    "null_state \<equiv> \<lambda>x. 0"
  syntax 
    "_State" :: "updbinds => 'a" ("<_>")
  translations
    "_State ms" == "_Update <> ms"
    "_State (_updbinds b bs)" <= "_Update (_State b) bs"
    
    
    
  datatype aexp = N int | V vname | Assign vname aexp | Plus aexp aexp (* Add assignment operator here *)
    
  text \<open>The function \<open>aval\<close> now returns a pair of value and new state.
    Use a case distinction (\<open>case \<dots> of (v,s) \<Rightarrow> \<dots>\<close>) or the (equivalent) 
    let-syntax for products (\<open>let (v,s) = \<dots> in \<dots>\<close>) to get hands on the 
    result value and the state from a pair.
  \<close>  
  fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<times> state" where
    "aval (N i) s = (i, s)" 
  | "aval (V x) s = (s x, s)"
  | "aval (Assign x a) s = (case aval a s of (v, s) \<Rightarrow> (v, s(x:=v)))"
  | "aval (Plus a1 a2) s = (case aval a1 s of (v1,s) \<Rightarrow> case aval a2 s of (v2,s) \<Rightarrow> (v1+v2,s))"  
    
  value "snd (aval (Assign ''x'' (N 5)) <>) ''x''"
    
  term "let (v1,s) = aval a1 s; (v2,s) = aval a2 s in (v1+v2,s)"  
    
    
  text \<open>Extend the constant folding to assignments! 
    Also consider assignments of the form \<open>x:=x\<close>!

    Do not try to move assignments, i.e., do not try to further optimize 
    an expression like \<open>(x := 4) + 7\<close>. 
  \<close>
  
  fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
    "plus (N x) (N y)  = N (x+y)"
  | "plus (N i) b = (if i=0 then b else Plus (N i) b)"
  | "plus a (N i) = (if i=0 then a else Plus a (N i))"
  | "plus a b = Plus a b"  
    
      
  fun assign :: "vname \<Rightarrow> aexp \<Rightarrow> aexp" where
    "assign x (V y) = (if x=y then V x else Assign x (V y))"
  | "assign x a = Assign x a"
  
  lemma aval_plus[simp]: "aval (plus a1 a2) s = aval (Plus a1 a2) s"
    apply (cases "(a1,a2)" rule: plus.cases) apply auto done
    (*  
    apply (induction a1 a2 rule: plus.induct)
    apply (auto)
    *)

  lemma aval_assign[simp]: "aval (assign x a) s = aval (Assign x a) s"
    apply (induction x a rule: assign.induct) apply auto done
      
  (* Prove a similar lemma for assign! *)
  
  fun asimp :: "aexp \<Rightarrow> aexp" where
    "asimp (N n) =  N n"
  | "asimp (V x) =  V x"  
  | "asimp (Assign x a) = assign x (asimp a)"  
  | "asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"  
    
    
  
  theorem aval_asimp[simp]: "aval (asimp a) s = aval a s"
    apply (induction a arbitrary: s)
    apply (auto split: prod.splits)
    done  

    
  subsection \<open>Compiling\<close>    

  (* Extend the stack machine with a \<open>STORE x\<close> instruction, that 
    pops the topmost stack value and stores it to variable \<open>x\<close>.
  *)  
    
  datatype instr = LOADI val | LOAD vname | STORE vname | ADD 
  type_synonym stack = "val list"
  
  (* The execute functions now works on pairs of state and stack. *)
  fun exec1  :: "instr \<Rightarrow> (state \<times> stack) \<Rightarrow> state \<times> stack" where 
    "exec1 (LOADI i) (s,stk) = (s, i#stk)"
  | "exec1 (LOAD x) (s,stk) = (s, s x#stk)"  
  | "exec1 (STORE x) (s,v#stk) = (s(x:=v), stk)"
  | "exec1 (ADD) (s,v1#v2#stk) = (s, (v1+v2) # stk)"
  | "exec1 _ _ = undefined"
    

  (* Nothing changes here, I only changed the name to sxstk for \<open>state \<times> stack\<close> *)
  fun exec :: "instr list \<Rightarrow> (state \<times> stack) \<Rightarrow> state \<times> stack" where
  "exec [] sxstk = sxstk" |
  "exec (i#is) sxstk = exec is (exec1 i sxstk)"
    
  lemma exec_append[simp]:
    "exec (is1@is2) sxstk = exec is2 (exec is1 sxstk)"
    apply (induction is1 arbitrary: sxstk)
    apply auto
    done  
    
    
  (* Compile arithmetic expressions with assignment, and show compiler correctness *)  
  hide_const (open) comp  

  fun comp :: "aexp \<Rightarrow> instr list" where
    "comp (N i) = [LOADI i]"
  | "comp (V x) = [LOAD x]"
  | "comp (Assign x a) = comp a @ [STORE x, LOAD x]"
  | "comp (Plus a1 a2) = comp a1 @ comp a2 @ [ADD]"  
  
  
  
  (* Hint: For assignment, a simple way is to LOAD the variable after one has STOREd it *)
  
  
  (* We phrased the theorem to be easily provable. 
    It is generally a good idea to write pairs explicitly,
    instead of accessing them with \<open>fst, snd\<close> etc.
  *)  
  theorem exec_comp:
    "aval a s = (v,s') \<Longrightarrow> exec (comp a) (s,stk) = (s',v#stk)"
    apply (induction a arbitrary: v s' s stk)
    apply (auto split: prod.splits)  
    done  
      
    (* Hint: Quite a lot of variables have to be generalized over (arbitrary).
      Use \<open>split: prod.splits\<close> to automatically split over case-distinctions 
      on pairs.
    *)  
    

end
