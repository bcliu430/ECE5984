chapter \<open>IMP with Arrays\<close>
theory IMPArrayHoarePartial
imports 
  Main 
  "~~/src/HOL/Library/Monad_Syntax" 
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Library/Rewrite"
begin

text \<open>
  Extension of IMP by generalized arrays and the common arithmetic and Boolean operations. 
  
  In this language, each variable stores a map from integers to integers.
  
  Initially, all integers are mapped to zero.
  
  In an expression, and on the LHS of an assignment, only indexed variables are allowed.
  That is, all expressions compute with single integers. 
  \<open> x[3] ::= y[0] + 5 \<close>
  
  The Clear operation resets the mapping of a variable to all zeroes.
  \<open>CLR x\<close>
  
  If the index is omitted, variables are indexed at zero. 
  This allows to use the variables as if they held single values.
  \<open>x ::= y + 5\<close> is the same as \<open>x[0] ::= y[0] + 5\<close>
  
  Summarized: 
    \<^item> Every variable is an array, but, by default, we only use index zero.
    \<^item> Arrays can be indexed by arbitrary integers (including negative ones), 
      and dynamically grow as needed.
\<close>


section \<open>Miscellaneous\<close>
(* Required to "instantiate" existential without introducing new variable, 
  which would not unify with already introduced schematic *)  
lemma ex_eq_some: "(\<exists>x. P x) \<longleftrightarrow> P (SOME x. P x)"
  by (meson someI)
  
section \<open>Syntax\<close>  

subsection \<open>Variables and Constants\<close>
type_synonym vname = string

type_synonym val = int

subsection \<open>Arithmetic Expressions\<close>
datatype aexp = 
    N int            -- \<open>Constant\<close>
  | V vname aexp     -- \<open>Array at index \<open>x[i]\<close>\<close> 
  | Binop "int \<Rightarrow> int \<Rightarrow> int" aexp aexp -- \<open>Binary operation\<close>

abbreviation "V0 x \<equiv> V (x) (N 0)" -- \<open>Abbreviation for \<open>x[0]\<close>\<close>


abbreviation "Plus \<equiv> Binop (op+)"
abbreviation "Minus \<equiv> Binop (op-)"
abbreviation "Times \<equiv> Binop (op*)"

text \<open>Warning, the following two also give defined results on division by zero!\<close>
value "a div (0::int)" value "a mod (0::int)"
abbreviation "Div \<equiv> Binop (op div)"
abbreviation "Mod \<equiv> Binop (op mod)"

subsection \<open>Boolean Expressions\<close>
datatype bexp = 
    Bc bool    -- \<open>True or False\<close>
  | Not bexp   -- \<open>Negation\<close>
  | BBop "bool\<Rightarrow>bool\<Rightarrow>bool" bexp bexp   -- \<open>Binary boolean operation\<close>
  | Cmpop "int \<Rightarrow> int \<Rightarrow> bool" aexp aexp -- \<open>Comparison operation\<close>

abbreviation "And \<equiv> BBop op \<and>"
abbreviation "Or \<equiv> BBop op \<or>"
abbreviation "BNEq \<equiv> BBop op \<noteq>"
abbreviation "BEq \<equiv> BBop op \<longleftrightarrow>"

abbreviation "Less \<equiv> Cmpop op <"
abbreviation "Leq \<equiv> Cmpop op \<le>"
abbreviation "Greater \<equiv> Cmpop op >"
abbreviation "Geq \<equiv> Cmpop op \<ge>"
abbreviation "Equal \<equiv> Cmpop op ="
abbreviation "NEqual \<equiv> Cmpop op \<noteq>"

subsection \<open>Commands\<close>

datatype
  com = SKIP 
      | Assign vname aexp aexp  -- \<open> Assignment to index of array. \<open>x[i] = a\<close>\<close>
      | Clear  vname            -- \<open> Set all indices of array to 0\<close>
      | Seq    com  com         -- \<open> Sequential composition \<open>c\<^sub>1; c\<^sub>2\<close>\<close>
      | If     bexp com com     -- \<open> Conditional. \<open>if (b) c\<^sub>1 else c\<^sub>2\<close>\<close>
      | While  bexp com         -- \<open> While loop. \<open>while (b) c\<close>\<close>

subsection \<open>Concrete Syntax\<close>

text \<open>Like the original IMP, we only expose a minimal syntax for commands by default\<close>

notation 
  Assign  ("_[_] ::= _" [1000,900, 41] 41) and
  Clear   ("CLR _" [41] 41) and
  Seq     ("_;;/ _"  [40, 41] 40) and
  If      ("(IF _/ THEN _/ ELSE _)"  [0, 0, 41] 41) and
  While   ("(WHILE _/ DO _)"  [0, 41] 41)
      
text \<open>Shortcut notation for assigning to index 0. \<close>
abbreviation Assign0 ("_ ::= _" [1000, 41] 41)
  where "x ::= v \<equiv> (x[N 0] ::= v)"

abbreviation true where "true \<equiv> Bc True"
abbreviation false where "false \<equiv> Bc False"
  
  
  
text \<open>
  However, we provide a bundle with somewhat more fancy syntax.
\<close>


abbreviation (input) "IMP_Variable \<equiv> V0"
syntax "_IMPVariable" :: "idt \<Rightarrow> aexp"
translations "CONST IMP_Variable" \<rightharpoonup> "_IMPVariable"

abbreviation (input) "IMP_VariableI \<equiv> V"
syntax "_IMPVariableI" :: "idt \<Rightarrow> aexp \<Rightarrow> aexp"
translations "CONST IMP_VariableI" \<rightharpoonup> "_IMPVariableI"

abbreviation (input) "IMP_Assign x v \<equiv> Assign x (N 0) v"
syntax "_IMPAssign" :: "idt \<Rightarrow> aexp \<Rightarrow> com"
translations "CONST IMP_Assign" \<rightharpoonup> "_IMPAssign"

abbreviation (input) "IMP_AssignI x i v \<equiv> Assign x i v"
syntax "_IMPAssignI" :: "idt \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> com"
translations "CONST IMP_AssignI" \<rightharpoonup> "_IMPAssignI"

abbreviation (input) "IMP_Clear x \<equiv> Clear x"
syntax "_IMPClear" :: "idt \<Rightarrow> com"
translations "CONST IMP_Clear" \<rightharpoonup> "_IMPClear"


ML \<open>
  structure IMP_Translation = struct
  
    val cfg_var_syntax = Attrib.setup_config_bool @{binding IMP_var_syntax} (K false)
  
    fun 
      var_tr ctxt [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] =
        c $ var_tr ctxt [t] $ u
    | var_tr _ [Free (str,_)] = Syntax.const (@{const_syntax V0}) $ HOLogic.mk_string str
    | var_tr _ ts = raise (TERM ("IMP_Variable",ts))

    fun 
      vari_tr ctxt [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u, it] =
        c $ vari_tr ctxt [t,it] $ u
    | vari_tr _ [Free (str,_),it] = Syntax.const (@{const_syntax V}) $ HOLogic.mk_string str $ it
    | vari_tr _ ts = raise (TERM ("IMP_VariableI",ts))

    fun 
      ass_tr ctxt [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u, rhst] =
        c $ ass_tr ctxt [t,rhst] $ u
    | ass_tr _ [Free (str,_),rhst] = Syntax.const (@{const_syntax Assign0}) $ HOLogic.mk_string str $ rhst
    | ass_tr _ ts = raise (TERM ("IMP_AssignI",ts))
    
    fun 
      assi_tr ctxt [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u, it, rhst] =
        c $ assi_tr ctxt [t,it,rhst] $ u
    | assi_tr _ [Free (str,_),it,rhst] = Syntax.const (@{const_syntax Assign}) $ HOLogic.mk_string str $ it $ rhst
    | assi_tr _ ts = raise (TERM ("IMP_Assign",ts))
    
    fun 
      clr_tr ctxt [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] =
        c $ clr_tr ctxt [t] $ u
    | clr_tr _ [Free (str,_)] = Syntax.const (@{const_syntax Clear}) $ HOLogic.mk_string str
    | clr_tr _ ts = raise (TERM ("IMP_Clear",ts))
    
    
    
    
    fun 
      dest_list_syntax (Const (@{const_syntax List.Cons},_)$x$xs) 
        = x::dest_list_syntax xs
    | dest_list_syntax (Const (@{const_syntax List.Nil},_)) = []
    | dest_list_syntax _ = raise Match
    
    fun 
      dest_char_syntax (Const (@{const_syntax String.Char}, _) $ c) = 
        let
          val n = Numeral.dest_num_syntax c
          val s = chr n
        in
          s
        end
    | dest_char_syntax _ = raise Match    
    
    fun dest_var_syntax t = let
      val s =
          dest_list_syntax t 
        |> map dest_char_syntax 
        |> implode
      val _ = Symbol.is_ascii_identifier s orelse raise Match  
    in
      s
    end
    
    fun 
      var_tr' _ [t:term] = 
        Syntax.const @{const_syntax "IMP_Variable"} $ Syntax.const (dest_var_syntax t)
    | var_tr' _ [t:term,it] =
        Syntax.const @{const_syntax "IMP_VariableI"} $ Syntax.const (dest_var_syntax t) $ it
    | var_tr' _ _ = raise Match

    fun 
      ass_tr' _ [t:term,vt] = 
        Syntax.const @{const_syntax "IMP_Assign"} $ Syntax.const (dest_var_syntax t) $ vt
    | ass_tr' _ [t:term,it,vt] =
        Syntax.const @{const_syntax "IMP_AssignI"} $ Syntax.const (dest_var_syntax t) $ it $ vt
    | ass_tr' _ _ = raise Match

    fun 
      clr_tr' _ [t:term] = 
        Syntax.const @{const_syntax "IMP_Clear"} $ Syntax.const (dest_var_syntax t)
    | clr_tr' _ _ = raise Match
    
    
    fun if_var_syntax f ctxt = 
      if Config.get ctxt cfg_var_syntax then
        f ctxt
      else
        raise Match
    
    
    val _ = Theory.setup (
      Sign.print_translation [
        (@{const_syntax "V0"}, if_var_syntax var_tr'),
        (@{const_syntax "V"}, if_var_syntax var_tr'),
        (@{const_syntax "Assign0"}, if_var_syntax ass_tr'),
        (@{const_syntax "Assign"}, if_var_syntax ass_tr'),
        (@{const_syntax "Clear"}, if_var_syntax clr_tr')
      ]
    )
    val _ = Theory.setup (
      Sign.parse_translation [
        (@{syntax_const "_IMPVariable"}, if_var_syntax var_tr),
        (@{syntax_const "_IMPVariableI"}, if_var_syntax vari_tr),
        (@{syntax_const "_IMPAssign"}, if_var_syntax ass_tr),
        (@{syntax_const "_IMPAssignI"}, if_var_syntax assi_tr),
        (@{syntax_const "_IMPClear"}, if_var_syntax clr_tr)
      ]
    )

    
  end
\<close>


consts 
  eplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" 
  eminus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   
  etimes :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   
  edivide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" 
  emodulo :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" 
  eequal :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  neequal :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  eless :: "'a \<Rightarrow> 'a \<Rightarrow> 'b" 
  egreater :: "'a \<Rightarrow> 'a \<Rightarrow> 'b" 

bundle IMP_Syntax begin

notation IMP_Variable ("$_" [100] 100)
notation IMP_VariableI ("_\<^bold>[_\<^bold>]" [100,100] 100)

no_notation 
  Assign0 ("_ ::= _" [1000, 41] 41) and
  Assign  ("_[_] ::= _" [1000,900, 41] 41) and
  Clear   ("CLR _" [41] 41)

notation 
  IMP_Assign ("_ ::= _" [1000, 41] 41) and
  IMP_AssignI  ("_\<^bold>[_\<^bold>] ::= _" [1000,0, 41] 41) and
  IMP_Clear   ("CLR _" [41] 41)

declare [[IMP_var_syntax]]


no_notation
  plus  (infixl "+" 65) and
  minus (infixl "-" 65) and
  times (infixl "*" 70) and
  divide (infixl "div" 70) and
  modulo (infixl "mod" 70)
  
notation 
  eplus   (infixl "+" 65)   and
  eminus  (infixl "-" 65)   and
  etimes  (infixl "*" 70)   and
  edivide (infixl "div" 70) and
  emodulo (infixl "mod" 70)
  
adhoc_overloading eplus plus Plus  
adhoc_overloading eminus minus Minus  
adhoc_overloading etimes times Times  
adhoc_overloading edivide divide Div  
adhoc_overloading emodulo modulo Mod  

notation Or (infixr "||" 30)
notation And (infixr "&&" 35)
notation Not ("!_" [90] 90)

no_notation "Pure.eq" (infix "==" 2)

notation 
  eequal  (infix "==" 50) and
  neequal (infix "!=" 50)

adhoc_overloading eequal BEq Equal  
adhoc_overloading neequal BNEq NEqual  


no_notation 
  less ("(_/ < _)"  [51, 51] 50) and
  greater  (infix ">" 50) and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  greater_eq  (infix ">=" 50)

notation 
  eless ("(_/ < _)"  [51, 51] 50) and
  egreater (infix ">" 50)
  
adhoc_overloading eless less Less  
adhoc_overloading egreater greater Greater  
  
notation
  Leq  ("(_/ <= _)" [51, 51] 50) and
  Geq  (infix ">=" 50)
  
end
  
  
subsection \<open>Syntax Overview\<close>

text \<open>Activate the Syntax locally in a context\<close>
context 
  includes IMP_Syntax 
begin

  subsubsection \<open>Arithmetic expressions\<close>
  
  text \<open>Idiosyncrasies: 
    \<^item> For array indexing, we use bold brackets \<open>\<^bold>[ \<^bold>]\<close>. Type \<open>\ bold [\<close> and \<open>\ bold ]\<close>
    \<^item> Prefixing a variable with \<open>$\<close> refers to index 0 of this variable. 
      This way, variables, which hold maps, can conveniently be used as single values.
  \<close>
  
  term "$foo"       term "V0 ''foo''"
  term "bar\<^bold>[N 3\<^bold>]"   term "V ''bar'' (N 3)" -- \<open>Type "\ bold [" and "\ bold ]" \<close>
  term "$a + $b"        term "Plus (V0 ''a'') (V0 ''b'')"
  term "$a + $b * $c"   term "Plus (V0 ''a'') (Times (V0 ''b'') (V0 ''c''))"
  term "($a + $b) * $c" term "Times (Plus (V0 ''a'') (V0 ''b'')) (V0 ''c'')"
  
  term "a\<^bold>[$i\<^bold>] + $b - $c*$d div $e mod $f"
  
  text \<open>Boolean Expressions\<close>
  text \<open>Idiosyncrasies: 
    \<^item> Not \<open>!\<close> binds with high priority, higher than any other operator
  \<close>
  
  term "$a < $b"
  term "$a > $b"
  term "$a <= $b"
  term "$a >= $b"
  term "$x == $y"
  term "$x != $y"
  
  term "true && false"
  term "true || false"
  term "true != false"
  term "true == true"
  
  term "(!true == false)  = ( (!true) == false )"
  term "!(true == false)"

  text \<open>Commands\<close>
  text \<open>Idiosyncrasies: 
    \<^item> Using \<open>::=\<close> for assignment, and, again, bold brackets for array indexing
  \<close>
  
  term "CLR x"                term "Clear ''x''"
  term "x ::= $a + N 1"       term "Assign0 ''x'' (Plus (V0 ''a'') (N 1))"
  term "x\<^bold>[$i\<^bold>] ::= $a + N 1"   term "Assign ''x'' (V0 ''i'') (Plus (V0 ''a'') (N 1))"


  term "x ::= $a;; y ::= $b"
  term "IF $x<N 5 THEN SKIP ELSE x::=$x - N 1"
  term "WHILE $x<N 5 DO x::=$x + N 1"
  
  
end


subsection \<open>Example Program\<close>
locale Imp_Array_Examples begin
unbundle IMP_Syntax
abbreviation "array_sum \<equiv> 
  CLR r;;             (* It's good practice to clear auxiliary variables before use *)
  r ::= N 0;;         (* Not strictly necessary, but documents that r is used as plain variable  *)
  WHILE $l < $h DO (
    r ::= $r + a\<^bold>[$l\<^bold>];;
    l ::= $l + (N 1)
  )"

term array_sum
  
end


section \<open>Semantics\<close>

subsection \<open>States and Configuration\<close>
text \<open>
  Each variable holds an unlimited amount of values, indexed by integers
\<close>
type_synonym state = "vname \<Rightarrow> (int \<Rightarrow> val)"
type_synonym config = "com \<times> state"

text {* A little syntax magic to write larger states compactly: *}

(* All variables hold zeroes initially.
*)
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>_ _. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

lemma null_state_app[simp]: "<> x = (\<lambda>_. 0)" by (auto simp: null_state_def)

text \<open>Constructing a generalized array from a list\<close>
definition list :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "list l i \<equiv> if 0\<le>i \<and> nat i<length l then l!nat i else 0"

text \<open>Plain variable: Value at index 0 only\<close>
abbreviation "var x \<equiv> list [x]"

lemma "var x i = (if i=0 then x else 0)" by (simp add: list_def) 
  
lemma list_nth[simp]: "\<lbrakk>0\<le>i; nat i<length l\<rbrakk> \<Longrightarrow> list l i = l!nat i"
  by (auto simp: list_def)
  
lemma list_subst[simp]: "\<lbrakk> 0\<le>i; nat i<length l \<rbrakk> \<Longrightarrow> (list l)(i:=x) = list (l[nat i:=x])"  
  by (auto simp: list_def intro!: ext)

lemma list_fold[simp]: "(\<lambda>_. 0)(0:=x) = var x"
  by (auto simp: list_def intro!: ext)

lemma list_inj[simp]: "length l = length l' \<Longrightarrow> list l = list l' \<longleftrightarrow> l=l'"
  apply (auto simp: list_def[abs_def] split: if_splits)
  by (metis (mono_tags, hide_lams) nat_int nth_equalityI of_nat_0_le_iff)
  
subsection \<open>Arithmetic Expressions\<close>

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x i) s = (s x) (aval i s)" |
"aval (Binop f a1 a2) s = f (aval a1 s) (aval a2 s)"

subsection \<open>Boolean Expressions\<close>

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s \<longleftrightarrow> v" |
"bval (Not b) s \<longleftrightarrow> \<not>(bval b s)" |
"bval (BBop f b1 b2) s \<longleftrightarrow> f (bval b1 s) (bval b2 s)" |
"bval (Cmpop f a1 a2) s \<longleftrightarrow> f (aval a1 s) (aval a2 s)"

subsection \<open>Big-Step\<close>
  
inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x[i] ::= a,s) \<Rightarrow> s(x := ((s x)(aval i s := aval a s)))" |
Clear: "(CLR x, s) \<Rightarrow> s(x:=(\<lambda>_. 0))" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue: "\<lbrakk> bval b s; (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"


subsubsection \<open>Automatic Derivation\<close>
text \<open>The following is a method to execute a configuration by deriving it's big-step semantics\<close>
method Bs_simp = simp add: list_def
method If = (rule IfTrue, (Bs_simp;fail)) | (rule IfFalse, (Bs_simp;fail))
method While = (rule WhileTrue, (Bs_simp;fail)) | (rule WhileFalse, (Bs_simp;fail))
method BigStep = simp?; ((rule Skip Assign Seq Clear) | If | While)
method BigSteps = BigStep+

context Imp_Array_Examples begin
  schematic_goal "(array_sum,<''l'':=list [1], ''h'':=list [5], ''a'':=list [100,1,2,3,4,200,300]>) \<Rightarrow> ?s"
    by BigSteps

end

subsubsection \<open>Proof Automation Setup\<close>
declare big_step.intros [intro]

lemmas big_step_induct = big_step.induct[split_format(complete)]

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"

inductive_cases AssignE[elim!]: "(x[i] ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases ClearE[elim!]: "(CLR x,s) \<Rightarrow> t"
thm ClearE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE


subsubsection \<open>Properties\<close>

text \<open>Sequential composition is associative\<close>
lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(c1, s) \<Rightarrow> s1" and
    c2: "(c2, s1) \<Rightarrow> s2" and
    c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  -- "The other direction is analogous"
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"
  thus "(c1;; c2;; c3, s) \<Rightarrow> s'" by auto
qed

text \<open>The big-step semantics is deterministic\<close>
theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
proof (induction arbitrary: u rule: big_step.induct)
  case (Skip s)
  then show ?case by auto
next
  case (Assign x i a s u)
  then show ?case by auto
next
  case (Clear x s)
  then show ?case by auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by blast
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  from IfTrue.prems IfTrue.hyps(1) IfTrue.IH
  show ?case by auto
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  from IfFalse.prems IfFalse.hyps(1) IfFalse.IH
  show ?case by auto
next
  case (WhileFalse b s c)
  then show ?case by auto
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3) then show ?case by blast
qed

subsection \<open>Small-Step\<close>
  
fun small_step :: "com * state \<Rightarrow> com * state" where
  "small_step (SKIP;;c\<^sub>2,s) = (c\<^sub>2,s)"  
| "small_step (x[i] ::= a, s) = (SKIP, s(x := ((s x)(aval i s := aval a s))))"
| "small_step (CLR x, s) = (SKIP, s(x:=(\<lambda>_. 0)))"
| "small_step (c\<^sub>1;;c\<^sub>2,s) = (let (c\<^sub>1',s) = small_step (c\<^sub>1,s) in (c\<^sub>1';;c\<^sub>2,s))"
| "small_step (IF b THEN c1 ELSE c2, s) = (if bval b s then (c1, s) else (c2, s))"
| "small_step (WHILE b DO c,s) = (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"
| "small_step (SKIP,s) = undefined"
  

abbreviation is_small_step (infix "\<rightarrow>" 55) 
  where "is_small_step cs cs' \<equiv> fst cs \<noteq> SKIP \<and> small_step cs = cs'"
  
abbreviation
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == (op \<rightarrow>)\<^sup>*\<^sup>* x y"

subsubsection{* Proof infrastructure *}

text{* The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form @{text"a \<rightarrow> b \<Longrightarrow> \<dots>"} where @{text a} and @{text b} are
not already pairs @{text"(DUMMY,DUMMY)"}. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
@{text"\<rightarrow>"} into pairs: *}
lemmas small_step_induct = small_step.induct[split_format(complete)]

subsubsection "Equivalence with big-step semantics"

lemma ss_seq2: "(c,s) \<rightarrow> (c',s') \<Longrightarrow> (c;;cx,s) \<rightarrow> (c';;cx,s')"
  by (induction c s arbitrary: c' s' rule: small_step_induct) auto

lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
  apply (induction rule: converse_rtranclp_induct2)
  apply (auto simp: ss_seq2 converse_rtranclp_into_rtranclp) 
  done

lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
proof -
  assume a1: "(c2, s2) \<rightarrow>* (SKIP, s3)"
  assume a2: "(c1, s1) \<rightarrow>* (SKIP, s2)"
  have "(SKIP;; c2, s2) \<rightarrow>* (SKIP, s3)"
    using a1 by (simp add: converse_rtranclp_into_rtranclp)
  then have "\<And>p. p \<rightarrow>* (SKIP, s3) \<or> \<not> p \<rightarrow>* (SKIP;; c2, s2)"
    by (metis (lifting) rtranclp.rtrancl_into_rtrancl rtranclp_idemp)
  then show ?thesis
    using a2 star_seq2 by blast
qed  
  
lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign then show ?case 
    by (auto intro!: r_into_rtranclp ext)
next
  case Clear then show ?case 
    by (auto intro!: r_into_rtranclp ext)
next
  case Seq thus ?case by (blast intro: seq_comp)
next
  case IfTrue thus ?case 
    by (auto intro: converse_rtranclp_into_rtranclp)
next
  case IfFalse thus ?case 
    by (auto intro: converse_rtranclp_into_rtranclp)
next
  case WhileFalse thus ?case
    by (fastforce intro: converse_rtranclp_into_rtranclp)
  
next
  case WhileTrue
  thus ?case
    apply (rule_tac converse_rtranclp_into_rtranclp)
    apply simp
    apply (rule_tac converse_rtranclp_into_rtranclp)
    apply simp
    by (simp add: seq_comp)
  
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction arbitrary: cs' t rule: small_step.induct)
apply (auto split: prod.splits if_splits)
done

lemma small_to_big:
  "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
apply (induction rule: converse_rtranclp_induct)
apply (auto intro: small1_big_continue)
done

text {*
  Finally, the equivalence theorem:
*}
theorem big_iff_small:
  "cs \<Rightarrow> t \<longleftrightarrow> cs \<rightarrow>* (SKIP,t)"
  using small_to_big big_to_small by blast


subsection \<open>Termination\<close>
definition "final cs \<equiv> \<nexists>cs'. cs\<rightarrow>cs'"

lemma SKIP_final[simp]: "final (c,s) \<longleftrightarrow> c=SKIP"
  by (auto simp: final_def)


section \<open>Hoare-Logic for Partial Correctness\<close>

type_synonym assn = "state \<Rightarrow> bool"

definition
hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> (assn) \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile> {P}c{Q} = (\<forall>s t. P s \<and> (c,s) \<Rightarrow> t \<longrightarrow> Q t)"

context
  notes [simp] = hoare_valid_def
begin
  lemma hoare_validI: 
    assumes "\<And>s t. \<lbrakk> P s; (c,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> Q t"
    shows "\<Turnstile> {P}c{Q}"
    using assms by auto
  
  lemma conseq_rule: 
    assumes "\<And>s. P s \<Longrightarrow> P' s"
    assumes "\<Turnstile> {P'} c {Q'}"
    assumes "\<And>s. Q' s \<Longrightarrow> Q s"
    shows "\<Turnstile> {P} c {Q}"
    using assms by auto
  
  (* One-sided versions of the consequence rule *)  
  lemma conseq_pre_rule: 
    assumes "\<Turnstile> {P'} c {Q}"
    assumes "\<And>s. P s \<Longrightarrow> P' s"
    shows "\<Turnstile> {P} c {Q}"
    using assms using conseq_rule by blast
  
  lemma conseq_post_rule: 
    assumes "\<And>s. Q s \<Longrightarrow> Q' s"
    assumes "\<Turnstile> {P} c {Q}"
    shows "\<Turnstile> {P} c {Q'}"
    using assms using conseq_rule by blast
  
  lemma skip_rule: "\<Turnstile> {P} SKIP {P}"
    by (auto simp: hoare_valid_def)
  
  lemma assign_rule: "\<Turnstile> {\<lambda>s. P (s( x := (s x)(aval i s := aval a s) )) } x[i]::=a {P}"
    by (auto)

  lemma clear_rule: "\<Turnstile> {\<lambda>s. P (s( x := (\<lambda>_. 0) )) } CLR x {P}"
    by (auto)
    
  lemma basic_seq_rule:
    assumes "\<Turnstile> {P} c\<^sub>1 {Q}" "\<Turnstile> {Q} c\<^sub>2 {R}"
    shows "\<Turnstile> {P} c\<^sub>1;;c\<^sub>2 {R}"
    using assms by auto
    
  lemma if_rule:  
    assumes "\<Turnstile> {P1} c\<^sub>1 {Q}" "\<Turnstile> {P2} c\<^sub>2 {Q}"
    shows "\<Turnstile> {\<lambda>s. if bval b s then P1 s else P2 s} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"
    using assms by auto
  
  lemma basic_while_rule:
    assumes "\<Turnstile> {\<lambda>s. P s \<and> bval b s} c {P}"
    shows "\<Turnstile> {P} WHILE b DO c {\<lambda>s. P s \<and> \<not> bval b s}"
  proof (rule hoare_validI)  
    fix s t
    assume "(WHILE b DO c, s) \<Rightarrow> t" "P s" 
    then show "P t \<and> \<not> bval b t"
    proof (induction "WHILE b DO c" s t rule: big_step_induct)
      case (WhileFalse s)
      then show ?case by simp
    next
      case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
      note IH = \<open>P s\<^sub>2 \<Longrightarrow> P s\<^sub>3 \<and> \<not> bval b s\<^sub>3\<close>
      
      from \<open>P s\<^sub>1\<close> \<open>bval b s\<^sub>1\<close> \<open>(c, s\<^sub>1) \<Rightarrow> s\<^sub>2\<close> \<open>\<Turnstile> {\<lambda>s. P s \<and> bval b s} c {P}\<close> have "P s\<^sub>2"
        unfolding hoare_valid_def by auto
      with IH show "P s\<^sub>3 \<and> \<not> bval b s\<^sub>3" .
    qed
  qed  
  
  
  text \<open>We swap the premises of the sequence rule, as our 
    verification condition generator will work on sequences 
    from right to left.\<close>
  lemma seq_rule:
    assumes "\<Turnstile> {Q} c\<^sub>2 {R}" "\<Turnstile> {P} c\<^sub>1 {Q}"
    shows "\<Turnstile> {P} c\<^sub>1;;c\<^sub>2 {R}"
    using basic_seq_rule assms by blast
  
  
  text \<open>We combine the while-rule with a consequence rule, to
    make it more usable in verification condition generation\<close>
  
  (* Explicit backwards derivation *)
  lemma while_rule:
    assumes "\<Turnstile> {R} c {P}"
    assumes "\<And>s. \<lbrakk>P s; bval b s\<rbrakk> \<Longrightarrow> R s"
    assumes "\<And>s. \<lbrakk>P s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q s"
    shows "\<Turnstile> {P} WHILE b DO c {Q}"
    apply (rule conseq_post_rule[where Q="\<lambda>s. P s \<and> \<not>bval b s"])
    apply (rule assms(3); simp)
    apply (rule basic_while_rule)
    apply (rule conseq_pre_rule)
    apply (rule assms(1))
    apply (rule assms(2); auto)
    done
    

end

section \<open>Verification Condition Generator\<close>

definition AWHILE :: "assn \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" ("(INVAR _ WHILE _/ DO _)"  [0, 0, 61] 61)
  where "INVAR I WHILE b DO c \<equiv> WHILE b DO c"

lemma annot_invar: "(WHILE b DO c) = (INVAR I WHILE b DO c)" by (simp add: AWHILE_def)
  
lemma awhile_rule:
  assumes "\<Turnstile> {R} c {P}"
  assumes "\<And>s. \<lbrakk>P s; bval b s\<rbrakk> \<Longrightarrow> R s"
  assumes "\<And>s. \<lbrakk>P s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q s"
  shows "\<Turnstile> {P} INVAR P WHILE b DO c {Q}"
  unfolding AWHILE_def by (rule while_rule[OF assms])

lemmas vcg_rules = skip_rule assign_rule clear_rule seq_rule if_rule awhile_rule


method vcg_step = clarsimp?;rule vcg_rules | (safe;clarsimp)
method vcg_present_nice_goal = clarsimp?, ((thin_tac "_=list _")+)?
method vcg_ctd = vcg_step+, vcg_present_nice_goal?
method vcg = rule conseq_pre_rule, vcg_ctd
  
  
end
