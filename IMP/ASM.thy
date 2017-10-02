section "Stack Machine and Compilation"

theory ASM imports AExp begin

subsection "Stack Machine"

text_raw{*\snip{ASMinstrdef}{0}{1}{% *}
datatype instr = LOADI val | LOAD vname | ADD
text_raw{*}%endsnip*}

text_raw{*\snip{ASMstackdef}{1}{2}{% *}
type_synonym stack = "val list"
text_raw{*}%endsnip*}

text \<open>Execution of a single instruction is straightforward, 
  except for the special case if one tries to execute ADD with 
  a stack of less than two elements. 
  We leave this case explicitly undefined, where undefined 
  is just an ordinary HOL term, but without any additional theorems on it.
  That is, @{term "undefined::'a"} may be every value of type @{typ 'a}, but 
  you don't know which one.
\<close>  
fun exec1  :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where 
  "exec1 (LOADI n) _ stk  =  n # stk"
| "exec1 (LOAD x) s stk  =  s(x) # stk"
| "exec1 ADD _ (a#b#stk) = (a+b)#stk"
| "exec1 ADD _ _ = undefined"   
  
  
text \<open>Executing a list of statements is straightforward\<close>
text_raw{*\snip{ASMexecdef}{1}{2}{% *}
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"
text_raw{*}%endsnip*}

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append[simp]:
  "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)"
apply(induction is1 arbitrary: stk)
apply (auto)
done


subsection "Compilation"

text \<open>Compilation of expressions to stack-machines is particularly easy:
  Each expression compiles to a program that effectively pushes its result
  to the top of stack.
\<close>
text_raw{*\snip{ASMcompdef}{0}{2}{% *}
fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"
text_raw{*}%endsnip*}

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

text \<open>This theorem intuitively states: When running the compiled program for 
  \<open>a\<close>, it will push the value of \<open>a\<close> on the stack, not changing anything on 
  the original stack.
\<close>  
theorem exec_comp: "exec (comp a) s stk = aval a s # stk"
apply(induction a arbitrary: stk)
apply (auto)
done

text \<open>Special case for starting with an empty stack. 
  Note, this theorem cannot be proved by induction directly, but needs 
  to be generalized to @{thm exec_comp} first.
\<close>  
theorem exec_comp': "exec (comp a) s [] = [aval a s]"
  by (simp add: exec_comp)
  
  
end
