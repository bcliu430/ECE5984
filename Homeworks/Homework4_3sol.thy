theory Homework4_3sol
imports Main "~~/src/HOL/Library/Code_Char"
begin

  (*
    ISSUED: Wednesday, October 11
    DUE: Wednesday, October 18, 11:59pm


    This is a bonus homework, worth 10 bonus points.
    Note that this homework is not too difficult to solve!
    All proofs can be found by following the standard heuristics presented
      in the lecture, although Isar might be useful to get more readable proofs.

    Even if you cannot solve everything, you can still skip proofs with sorry
    and try to work on the next sub-tasks.
  *)

  
  (*
    In this homework, we are going to implement a simple globbing algorithm,
    i.e., a function that decides whether, e.g., \<open>*.thy\<close> matches \<open>Homework.thy\<close>.
  *)
  
  section \<open>Parsing of Patterns\<close>

  hide_const (open) Char  
    
  (*
    Internally, we represent a glob pattern by a list of symbols, each symbol
    either being a character to be matched literally, or a star to be matched
    by any sequence of characters:
  *)
  datatype symbol = Char char | Star
  type_synonym pattern = "symbol list"  

  (*
    However, the input shall be a string, using \<open>*\<close> to represent any number
    of symbols. 
    
    Thus a single character of the string is parsed by the following function:
  *)  
  definition parse_symbol :: "char \<Rightarrow> symbol" where
    "parse_symbol x = (if x=CHR ''*'' then Star else Char x)"

  (*
    Unfortunately, it has become a common habit to write special 
    characters in file names. In order to be general, we want to allow an 
    escape character in our glob patterns. As \ is hard to type in Isabelle 
    strings, we choose ! as escape character. That is, whatever character 
    follows ! will be interpreted literally. An ! at the end of the string 
    has no special meaning.  

    The parser effectively maps parse_symbol over the input, 
    adding some special case to handle the escape character.

    Replace the \<open>undefined\<close> gaps by meaningful code!
  *)  

  fun parse :: "string \<Rightarrow> pattern" where
    "parse [] = []"
  | "parse (x#xs) = (
      if x=CHR ''!'' then 
        (case xs of [] \<Rightarrow> (*<*)[Char x](*>*) | y#ys \<Rightarrow> (*<*)Char y#parse ys(*>*) ) 
      else 
        (*<*)parse_symbol x#parse xs(*>*)  )"

  (* Test cases *)
  (* No escape characters *)
  value \<open>parse ''*.thy'' = [Star, Char CHR ''.'', Char CHR ''t'', Char CHR ''h'', Char CHR ''y'']\<close>
    
  (* Escaping a * *)  
  value \<open>parse ''A!*.*'' = [Char CHR ''A'', Char CHR ''*'', Char CHR ''.'', Star]\<close>
    
  (* Escaping a !, escaping a *, ! as last character has no special meaning *)
  value \<open>parse ''*.c!!!*!'' = [Star, Char CHR ''.'', Char CHR ''c'', Char CHR ''!'', Char CHR ''*'', Char CHR ''!''] \<close>
    

  (*
    In order to show that our parser makes sense, we also define a pretty-printer,
    which translates a given list of symbols to a string, which, when parsed, yields
    the given list of symbols again \<open>parse (pretty syms) = syms\<close>.
    Thus, we can be sure that every list of symbols has a string representation.

    As pretty-printer output shall be pretty, do only insert escape characters
    where necessary, with one exception: You shall still escape a ! at the end 
    of the string, also this would not be necessary. (It will make the code 
    cleaner, and the pretty-printer does not rely on the somewhat odd handling 
    of escape-characters at the end of the string! )

    Fill in the gaps of the pretty-printer function:
  *)  
    
  fun pretty :: "pattern \<Rightarrow> string" where
    "pretty [] = (*<*)[](*>*)"
  | "pretty (Char x#xs) = (
      if (*<*)x=CHR ''!'' \<or> x=CHR ''*''(*>*) then (* Check whether character has to be escaped *)
        CHR ''!''#x#pretty xs 
      else 
        (*<*)x#pretty xs(*>*))"
  | "pretty (Star#xs) = (*<*)(CHR ''*''#pretty xs)(*>*)"
    

  (* Test cases *)
  value \<open>pretty [Star,Char CHR ''x''] = ''*x''\<close>  
  value \<open>pretty [Char CHR ''*''] = ''!*''\<close>  
  value \<open>pretty [Char CHR ''!'',Char CHR ''!'',Char CHR ''!''] = ''!!!!!!''\<close>
    (* The pretty printer should not exploit the special case of ! at the end of the string.
      That is, also the last ! character should be escaped! *)
    
  (* Proof that, for any pattern \<open>syms\<close>, parsing its pretty-print yields 
      the pattern again.

    Hint: pretty uses a complex pattern \<longrightarrow> computation induction! 
    Hint: unfold definitions if necessary, by adding the _def-lemma to the simpset.
  *)
  lemma "parse (pretty syms) = syms"
    apply (induction syms rule: pretty.induct)
    apply (auto simp: parse_symbol_def)
    done  

      
  (**** Not that important *****)    
  value "pretty (parse ''*c!*!'')"    
      
  fun wf :: "string \<Rightarrow> bool" where
    "wf [] \<longleftrightarrow> True"
  | "wf (x#xs) = (if x=CHR ''!'' then (case xs of [] \<Rightarrow> False | y#ys \<Rightarrow> y\<in>set ''!*'' \<and> wf ys) else wf xs)"  

  lemma "wf (pretty s)"
    apply (induction s rule: pretty.induct)
    apply (auto)
    done  
    
  lemma "wf s \<Longrightarrow> pretty (parse s) = s"
    apply (induction s rule: wf.induct)
    apply (auto split: list.splits simp: parse_symbol_def)  
    done
  (**** ***************** *****)    
      
      
  section \<open>Matching\<close>  
    
  (*
    Next, we want to define the semantics of a pattern.
    This can be elegantly done by inductive predicates as follows:

    Single symbol match:
      (C) The symbol Char c matches the string [c].
      (S) The symbol Star matches any string

      (E) The empty pattern matches the empty string
      (A) If symbol s matches xs, and pattern ss matches ys, then pattern s#ss matches xs@ys
  *)  
    
  inductive matchc :: "symbol \<Rightarrow> string \<Rightarrow> bool" where
    C[simp, intro]: "matchc (Char c) [c]"
  | S[simp, intro]: "matchc Star _"
    
    
  inductive match :: "pattern \<Rightarrow> string \<Rightarrow> bool" where
    E[simp]: "match [] []"
  | A: (*<*) "matchc s xs \<Longrightarrow> match ss ys \<Longrightarrow> match (s#ss) (xs@ys)" (*>*)
      (* Replace this by the rule (A) from the above textual description *)


  (* We can use forward reasoning to explicitly derive matches: *)  
  lemma "match (parse ''H*d'') ''Hello World''"
    using A[OF C[of "CHR ''H''"] A[OF S[of "''ello Worl''"] A[OF C[of "CHR ''d''"] E]]]
      (* Note: If your rule A has the premises the other way round, the above
        will yield an error. In this case, it's probably the best to swap
        the premises of your rule A.
      *)
    by (simp add: parse_symbol_def)

  (* FALLBACK: If you did not manage to write the parser, parse the pattern manually: *)      
  lemma "match [Char CHR ''H'', Star, Char CHR ''d''] ''Hello World''"
    using A[OF C[of "CHR ''H''"] A[OF S[of "''ello Worl''"] A[OF C[of "CHR ''d''"] E]]]
    by simp  
        
  (* Use the same technique to derive the following match! *)      

  lemma "match (parse ''*.thy'') ''Scratch.thy''"
    (*<*)using A[OF S[of "''Scratch''"] A[OF C[of "CHR ''.''"] A[OF C[of "CHR ''t''"] A[OF C[of "CHR ''h''"] A[OF C[of "CHR ''y''"] E ]]]]]
    by (simp add: parse_symbol_def)
    (*>*)
      
  (* FALLBACK: *)
  lemma "match [Star,Char CHR ''.'', Char CHR ''t'', Char CHR ''h'', Char CHR ''y''] ''Scratch.thy''"
    (*<*)using A[OF S[of "''Scratch''"] A[OF C[of "CHR ''.''"] A[OF C[of "CHR ''t''"] A[OF C[of "CHR ''h''"] A[OF C[of "CHR ''y''"] E ]]]]]
    by simp  
    (*>*)
      
      
  subsection \<open>Equations for Match\<close>     
  (*
    In a next step, we want to derive recursion equations for match.

    Show that the following equations hold!
  *)  
    
  lemma match_empty[simp]: "match [] xs \<longleftrightarrow> xs=[]"
    (*<*)
    by (auto elim: match.cases)
    (*>*)
    
  lemma match_cons[simp]: "match (s#ss) xs \<longleftrightarrow> (\<exists>xs1 xs2. xs=xs1@xs2 \<and> matchc s xs1 \<and> match ss xs2)"
    (*<*)
    apply (auto intro: match.intros)
    apply (erule match.cases)  
    apply auto
    done  
    (*>*)

  (* Having proved the above equations, we can actually use induction on the
    list of symbols to reason about match.

    Prove the following lemma by structural induction on a suitable 
    list-typed variable!

    Hint: Generalization will be required.
    Hint: Sledgehammer might help to complete the proof.
  *)    
  lemma match_append[simp]: 
    "match (ss1@ss2) xs \<longleftrightarrow> (\<exists>xs1 xs2. xs=xs1@xs2 \<and> match ss1 xs1 \<and> match ss2 xs2)"
    apply (induction ss1 arbitrary: xs)
    apply (auto)
    apply (metis append.assoc)
    by blast  

section \<open>Functional Implementation of a (naive) Globbing Algorithm\<close>      
      
  (* A disadvantage of inductive predicates is that they yield no simp-lemmas
    that could be used to evaluate a function.

    For example, the following command does not yield the expected result, but
    evaluation gets stuck early:
  *)
  value "match (parse ''*.thy'') ''Scratch.thy''"

  subsection \<open>Deriving Structural Equations\<close>  
    
  (* A first step to a functional implementation is to prove 
    structural equations for the inductive predicate. We have already done this 
      for match, now we do the same for matchc!

    Hint: The equations are not recursive, i.e., matchc does not occur on the right hand side.
  *)
  lemma matchc_Char[simp]: "matchc (Char c) xs \<longleftrightarrow> (*<*)xs=[c](*>*)"
    (*<*)
    by (simp add: matchc.simps)
    (*>*)  
   
  lemma matchc_Star[simp]: "matchc Star xs \<longleftrightarrow> True" by simp

  (* Having derived the recursion equations, we can define a function
    with the same equations. (If termination can be proved)

    Use the same right hand sides as above!
  *)    
  fun fmatchc :: "symbol \<Rightarrow> string \<Rightarrow> bool" where
    "fmatchc (Char c) xs \<longleftrightarrow> (*<*)xs=[c](*>*)"
  | "fmatchc (Star) _ \<longleftrightarrow> (*<*)True(*>*)"
    
  (*
    Prove that the functional version equals the inductive one.
    Hint: As we have shown the same recursion equations for matchc and fmatchc,
      this can be directly proved by induction over the symbol 
      (or, equivalently, case-distinction over the symbol)

  *)    
  lemma fmatchc_eq_matchc: "fmatchc s xs = matchc s xs"
    by (induction s) (auto)

  (*<*)  
  lemma "fmatchc s xs = matchc s xs"
    by (metis fmatchc.elims(2) fmatchc.simps(1) fmatchc.simps(2) matchc.simps)
  (*>*)  

      
  (* Do the same for match: Define fmatch, based on the recursion
    equations that we have derived earlier.

    Hint: Be sure to use fmatch and fmatchc also on the right hand sides!
  *)    
  thm match_empty match_cons    

  fun fmatch :: "symbol list \<Rightarrow> char list \<Rightarrow> bool" where   
    (*<*)
    "fmatch [] xs \<longleftrightarrow> xs=[]"
  | "fmatch (s#ss) xs \<longleftrightarrow> (\<exists>xs1 xs2. xs = xs1 @ xs2 \<and> fmatchc s xs1 \<and> fmatch ss xs2)"
    (*>*)
    
  (*
    Hints: Induction, you'll need generalization on some variable, 
      do not forget to use fmatchc_eq_matchc!
  *)  
  lemma fmatch_eq_match: "fmatch ss xs = match ss xs" 
    (*<*)
    by (induction ss arbitrary: xs) (auto simp: fmatchc_eq_matchc)
    (*>*)

  subsection \<open>Naive Iteration over all possible List-Splits\<close>  
      
  (*
    Let's test how close we are to an executable algorithm:
  *)    
  (* value "fmatch (parse ''*.thy'') ''Scratch.thy''" *) (* Fails! *)
    
  (* The problem is that the term \<open>\<exists>xs1 xs2. \<dots>\<close> cannot be evaluated.

    In the next step, we design a function to decide a term of the form:
      \<open>(\<exists>xs1 xs2. xs = xs1 @ xs2 \<and> P xs1 \<and> Q xs2)\<close> for predicates P Q.
  
    The idea is to exhaustively test all possibilities for the split of
    xs into xs1 and xs2. 

    For that purpose, we start with the split []@xs. 
    If this satisfies P and Q, we are done. Otherwise, we append
    the first character of xs to the first part of the split, and continue.
  
    E.g., for xs=[1,2,3], we would test, in that order:
      P [] \<and> Q [1,2,3]
      P [1] \<and> Q [2,3]
      P [1,2] \<and> Q [3]
      P [1,2,3] \<and> Q []
      
    Write a recursive function ex_split, such that
      ex_split P Q [] xs \<longleftrightarrow> (\<exists>xs1 xs2. xs=xs1@xs2 \<and> P (xs1) \<and> Q xs2)

    Hint: The function can be defined with two equations
      "ex_split P Q xs [] \<longleftrightarrow> \<dots>"
    | "ex_split P Q xs (y#ys) \<longleftrightarrow> \<dots>"  

    Do not use any quantifiers on the right hand sides!
  *)    
      
      
  fun ex_split :: "('a list \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  (*<*)  
    "ex_split P Q xs [] \<longleftrightarrow> P xs \<and> Q []"
  | "ex_split P Q xs (y#ys) \<longleftrightarrow> P xs \<and> Q (y#ys) \<or> ex_split P Q (xs@[y]) ys"  
  (*>*)

  (*<*)  
  lemma ex_split_eq_gen: "ex_split P Q xs ys \<longleftrightarrow> (\<exists>ys1 ys2. ys=ys1@ys2 \<and> P (xs@ys1) \<and> Q ys2)"
    apply (induction ys arbitrary: xs)
    apply (auto simp: Cons_eq_append_conv)
    apply force  
    done
  (*>*)    
    
  (* Show that ex_split does the right thing.
    Hint: You will need to generalize the lemma before induction works!
  *)    
  lemma ex_split_eq: "ex_split P Q [] xs \<longleftrightarrow> (\<exists>xs1 xs2. xs=xs1@xs2 \<and> P (xs1) \<and> Q xs2)"
  (*<*)  
    by (simp add: ex_split_eq_gen)
  (*>*)  

  subsection \<open>Combining Everything to Executable Matcher\<close>    
      
  (* Now, you should be able to define the following function: *)
  fun fmatch' where   
    "fmatch' [] s \<longleftrightarrow> s=[]"
  | "fmatch' (p#ps) s \<longleftrightarrow> ex_split (fmatchc p) (fmatch' ps) [] s"

  (* And show that it equals fmatch *)  
  lemma fmatch'_eq_fmatch: "fmatch' p s = fmatch p s" 
    (*<*)
    by (induction p arbitrary: s) (auto simp: fmatchc_eq_matchc ex_split_eq)
    (*>*)  

  (* A simple forward reasoning step yields the overall correctness lemma: *)
  lemmas fmatch'_correct = trans[OF fmatch'_eq_fmatch fmatch_eq_match]
      
  (* Test Cases *)  
  value "fmatch' (parse '''') ''''"
  value "fmatch' (parse ''*'') ''''"
  value "fmatch' (parse ''*******a*****'') ''abc''"
  value "fmatch' (parse ''*.thy'') ''Homework1.thy''"
  value "fmatch' (parse ''*!!.thy'') ''Homework!.thy''"
  value "fmatch' (parse ''*o*.thy'') ''Homework1.thy''"
  value "fmatch' (parse ''*o*.thy'') ''Parser.thy'' = False"
  value "fmatch' (parse ''H*d!!'') ''Hello World!''"
  value "fmatch' (parse ''F!*.*'') ''F*.cpp''"
  value "fmatch' (parse ''H*o*r*1.thy'') ''Homework1.thy''"
      
      
end
