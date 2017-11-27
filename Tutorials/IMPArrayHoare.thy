chapter \<open>IMP with Arrays\<close>
theory IMPArrayHoare
imports 
  Main 
  "~~/src/HOL/Library/Monad_Syntax" 
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Library/Rewrite"
begin

ML_val \<open>
  open Splitter
\<close>

ML \<open>
  local
    val ctxt = @{context} |> Splitter.del_split @{thm if_split}
    val ctxt = ctxt 
      delsimps @{thms fun_upd_apply}
      addsimps @{thms fun_upd_same fun_upd_other}
  in  
    val IMP_basic_ss = Simplifier.simpset_of ctxt
  end
\<close>

setup \<open>
  let
    open Simplifier
  
    (* FIXME: Copied from Simplifier, as these things are not exposed to the user *)
    
    val simpN = "simp";
    val congN = "cong";
    val onlyN = "only";
    val no_asmN = "no_asm";
    val no_asm_useN = "no_asm_use";
    val no_asm_simpN = "no_asm_simp";
    val asm_lrN = "asm_lr";
    
    
    val simp_options =
     (Args.parens (Args.$$$ no_asmN) >> K simp_tac ||
      Args.parens (Args.$$$ no_asm_simpN) >> K asm_simp_tac ||
      Args.parens (Args.$$$ no_asm_useN) >> K full_simp_tac ||
      Args.parens (Args.$$$ asm_lrN) >> K asm_lr_simp_tac ||
      Scan.succeed asm_full_simp_tac);
  
    fun transform_context f (ctxt,ts) = ((),(Context.map_proof f ctxt,ts))  
      
    fun simp_method more_mods meth =
      Scan.lift simp_options --| transform_context (put_simpset IMP_basic_ss) --|
        Method.sections (more_mods @ simp_modifiers') >>
        (fn tac => fn ctxt => METHOD (fn facts => meth ctxt tac facts));
    
    (** setup **)
    
    fun method_setup more_mods =
      Method.setup @{binding imp_basic_simp}
        (simp_method more_mods (fn ctxt => fn tac => fn facts =>
          HEADGOAL (Method.insert_tac ctxt facts THEN'
            (CHANGED_PROP oo tac) ctxt)))
        "simplification with basic simpset for IMP"  
  in
    method_setup []
  end
\<close>





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
  Assign  ("(_[_] ::= _)" [1000,900, 41] 41) and
  Clear   ("(CLR _)" [41] 41) and
  Seq     ("(_;;/ _)"  [40, 41] 40) and
  If      ("(IF (\<open>unbreakable\<close>_) THEN(2/ _/ )ELSE(2/ _))"  [0, 0, 41] 41) and
  While   ("(WHILE (\<open>unbreakable\<close>_) DO(2/ _))"  [0, 41] 41)
      
text \<open>Shortcut notation for assigning to index 0. \<close>
abbreviation Assign0 ("(_ ::= _)" [1000, 41] 41)
  where "x ::= v \<equiv> (x[N 0] ::= v)"

abbreviation true where "true \<equiv> Bc True"
abbreviation false where "false \<equiv> Bc False"
  

  
text \<open>
  However, we provide a bundle with somewhat more fancy syntax.
\<close>

abbreviation (input) "IMP_Variable \<equiv> V0"
syntax "_IMPVariable" :: "id \<Rightarrow> aexp"
translations "CONST IMP_Variable" \<rightharpoonup> "_IMPVariable"

abbreviation (input) "IMP_VariableI \<equiv> V"
syntax "_IMPVariableI" :: "id \<Rightarrow> aexp \<Rightarrow> aexp"
translations "CONST IMP_VariableI" \<rightharpoonup> "_IMPVariableI"

abbreviation (input) "IMP_Assign x v \<equiv> Assign x (N 0) v"
syntax "_IMPAssign" :: "id \<Rightarrow> aexp \<Rightarrow> com"
translations "CONST IMP_Assign" \<rightharpoonup> "_IMPAssign"

abbreviation (input) "IMP_AssignI x i v \<equiv> Assign x i v"
syntax "_IMPAssignI" :: "id \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> com"
translations "CONST IMP_AssignI" \<rightharpoonup> "_IMPAssignI"

abbreviation (input) "IMP_Clear x \<equiv> Clear x"
syntax "_IMPClear" :: "id \<Rightarrow> com"
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
  Assign0 ("(_ ::= _)" [1000, 41] 41) and
  Assign  ("(_[_] ::= _)" [1000,900, 41] 41) and
  Clear   ("(CLR _)" [41] 41)

notation 
  IMP_Assign ("(_ ::= _)" [1000, 41] 41) and
  IMP_AssignI  ("(_\<^bold>[_\<^bold>] ::= _)" [1000,0, 41] 41) and
  IMP_Clear   ("(CLR _)" [41] 41)

declare [[IMP_var_syntax]]

notation N ("\<acute>_" [105] 105)


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
  eless (infix "<"  50) and
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
  term "bar\<^bold>[\<acute>3\<^bold>]"   term "V ''bar'' (N 3)" -- \<open>Type "\ bold [" and "\ bold ]" \<close>

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
  term "x ::= $a + \<acute>1"       term "Assign0 ''x'' (Plus (V0 ''a'') (N 1))"
  term "x\<^bold>[$i\<^bold>] ::= $a + \<acute>1"   term "Assign ''x'' (V0 ''i'') (Plus (V0 ''a'') (N 1))"


  term "x ::= $a;; y ::= $b"
  term "IF $x<\<acute>5 THEN SKIP ELSE x::=$x - \<acute>1"
  term "WHILE $x<\<acute>5 DO x::=$x + \<acute>1"
  
  
end


subsection \<open>Example Program\<close>
locale Imp_Array_Examples begin
unbundle IMP_Syntax
abbreviation "array_sum \<equiv> 
  CLR r;;             (* It's good practice to clear auxiliary variables before use *)
  r ::= N 0;;         (* Not strictly necessary, but documents that r is used as plain variable  *)
  WHILE $l < $h DO (
    r ::= $r + a\<^bold>[$l\<^bold>];;
    l ::= $l + (\<acute>1)
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
definition vlist :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "vlist l i \<equiv> if 0\<le>i \<and> nat i<length l then l!nat i else 0"

text \<open>Plain variable: Value at index 0 only\<close>
abbreviation "var x \<equiv> vlist [x]"

lemma list_nth[simp]: "\<lbrakk>0\<le>i; nat i<length l\<rbrakk> \<Longrightarrow> vlist l i = l!nat i"
  by (auto simp: vlist_def)
  
lemma list_subst[simp]: "\<lbrakk> 0\<le>i; nat i<length l \<rbrakk> \<Longrightarrow> (vlist l)(i:=x) = vlist (l[nat i:=x])"  
  by (auto simp: vlist_def intro!: ext)

lemma list_fold[simp]: "(\<lambda>_. 0)(0:=x) = var x"
  by (auto simp: vlist_def intro!: ext)

lemma list_inj[simp]: "length l = length l' \<Longrightarrow> vlist l = vlist l' \<longleftrightarrow> l=l'"
  apply (auto simp: vlist_def[abs_def] split: if_splits)
  by (metis (mono_tags, hide_lams) nat_int nth_equalityI of_nat_0_le_iff)
  
definition "imap \<equiv> id"  
lemma imap_app[simp]: "imap a = a" by (auto simp: imap_def)
  
  
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
method Bs_simp = simp add: vlist_def
method If = (rule IfTrue, (Bs_simp;fail)) | (rule IfFalse, (Bs_simp;fail))
method While = (rule WhileTrue, (Bs_simp;fail)) | (rule WhileFalse, (Bs_simp;fail))
method BigStep = simp?; ((rule Skip Assign Seq Clear) | If | While)
method BigSteps = BigStep+

context Imp_Array_Examples begin
  schematic_goal "(array_sum,<''l'':=vlist [1], ''h'':=vlist [5], ''a'':=vlist [100,1,2,3,4,200,300]>) \<Rightarrow> ?s"
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
hoare_valid :: "('a \<Rightarrow> assn) \<Rightarrow> com \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile> {P}c{Q} = (\<forall>s t z. P z s \<and> (c,s) \<Rightarrow> t \<longrightarrow> Q z t)"

context
  notes [simp] = hoare_valid_def
begin
  lemma hoare_validI: 
    assumes "\<And>s t z. \<lbrakk> P z s; (c,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> Q z t"
    shows "\<Turnstile> {P}c{Q}"
    using assms by auto
  
  lemma conseq_rule: 
    assumes "\<And>s z. P z s \<Longrightarrow> P' z s"
    assumes "\<Turnstile> {P'} c {Q'}"
    assumes "\<And>s z. Q' z s \<Longrightarrow> Q z s"
    shows "\<Turnstile> {P} c {Q}"
    using assms by force
  
  (* One-sided versions of the consequence rule *)  
  lemma conseq_pre_rule: 
    assumes "\<Turnstile> {P'} c {Q}"
    assumes "\<And>z s. P z s \<Longrightarrow> P' z s"
    shows "\<Turnstile> {\<lambda>z. P z} c {\<lambda>z. Q z}"
    using assms using conseq_rule by blast
  
  lemma conseq_post_rule: 
    assumes "\<And>z s. Q z s \<Longrightarrow> Q' z s"
    assumes "\<Turnstile> {P} c {Q}"
    shows "\<Turnstile> {P} c {Q'}"
    using assms using conseq_rule by blast
  
  lemma skip_rule: "\<Turnstile> {P} SKIP {P}"
    by (auto)
  
  lemma assign_rule: "\<Turnstile> {\<lambda>z s. P z (s( x := (s x)(aval i s := aval a s) )) } x[i]::=a {P}"
    by (auto)

  lemma clear_rule: "\<Turnstile> {\<lambda>z s. P z (s( x := (\<lambda>_. 0) )) } CLR x {P}"
    by (auto)
    
  lemma basic_seq_rule:
    assumes "\<Turnstile> {P} c\<^sub>1 {Q}" "\<Turnstile> {Q} c\<^sub>2 {R}"
    shows "\<Turnstile> {P} c\<^sub>1;;c\<^sub>2 {R}"
    using assms by force
    
  definition "COND b P Q \<equiv> if b then P else Q"
  
  lemma if_rule:  
    assumes "\<Turnstile> {P1} c\<^sub>1 {Q}" "\<Turnstile> {P2} c\<^sub>2 {Q}"
    shows "\<Turnstile> {\<lambda>z s. COND (bval b s) (P1 z s) (P2 z s)} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"
    using assms unfolding COND_def by auto
  
  lemma basic_while_rule:
    assumes "\<Turnstile> {\<lambda>z s. P z s \<and> bval b s} c {P}"
    shows "\<Turnstile> {P} WHILE b DO c {\<lambda>z s. P z s \<and> \<not> bval b s}"
  proof (rule hoare_validI)  
    fix z s t
    assume "(WHILE b DO c, s) \<Rightarrow> t" "P z s" 
    then show "P z t \<and> \<not> bval b t"
    proof (induction "WHILE b DO c" s t rule: big_step_induct)
      case (WhileFalse s)
      then show ?case by simp
    next
      case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
      note IH = \<open>P z s\<^sub>2 \<Longrightarrow> P z s\<^sub>3 \<and> \<not> bval b s\<^sub>3\<close>
      
      from \<open>P z s\<^sub>1\<close> \<open>bval b s\<^sub>1\<close> \<open>(c, s\<^sub>1) \<Rightarrow> s\<^sub>2\<close> \<open>\<Turnstile> {\<lambda>z s. P z s \<and> bval b s} c {P}\<close> have "P z s\<^sub>2"
        unfolding hoare_valid_def by auto
      with IH show "P z s\<^sub>3 \<and> \<not> bval b s\<^sub>3" .
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
    assumes "\<And>z s. \<lbrakk>P z s; bval b s\<rbrakk> \<Longrightarrow> R z s"
    assumes "\<And>z s. \<lbrakk>P z s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q z s"
    shows "\<Turnstile> {P} WHILE b DO c {Q}"
    apply (rule conseq_post_rule[where Q="\<lambda>z s. P z s \<and> \<not>bval b s"])
    apply (rule assms(3); simp)
    apply (rule basic_while_rule)
    apply (rule conseq_pre_rule)
    apply (rule assms(1))
    apply (rule assms(2); auto)
    done
    

end


section \<open>Hoare-Logic for Total Correctness\<close>

definition
hoaret_valid :: "('a \<Rightarrow> assn) \<Rightarrow> com \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>t {P}c{Q} = (\<forall>z s. P z s \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow> t \<and> Q z t))"

context
  notes [simp] = hoaret_valid_def
begin
  lemma hoaret_validI: 
    assumes "\<And>z s. P z s \<Longrightarrow> \<exists>t. (c,s) \<Rightarrow> t \<and> Q z t"
    shows "\<Turnstile>\<^sub>t {P}c{Q}"
    using assms by auto
  
  lemma conseq_trule: 
    assumes "\<And>z s. P z s \<Longrightarrow> P' z s"
    assumes "\<Turnstile>\<^sub>t {P'} c {Q'}"
    assumes "\<And>z s. Q' z s \<Longrightarrow> Q z s"
    shows "\<Turnstile>\<^sub>t {P} c {Q}"
    using assms by force
  
  (* One-sided versions of the consequence rule *)  
  lemma conseq_pre_trule: 
    assumes "\<Turnstile>\<^sub>t {P'} c {Q}"
    assumes "\<And>z s. P z s \<Longrightarrow> P' z s"
    shows "\<Turnstile>\<^sub>t {\<lambda>z. P z} c {\<lambda>z. Q z}"
    using assms using conseq_trule by blast
  
  lemma conseq_post_trule: 
    assumes "\<And>z s. Q z s \<Longrightarrow> Q' z s"
    assumes "\<Turnstile>\<^sub>t {P} c {Q}"
    shows "\<Turnstile>\<^sub>t {P} c {Q'}"
    using assms using conseq_trule by metis
  
  lemma skip_trule: "\<Turnstile>\<^sub>t {P} SKIP {P}"
    by (auto)
  
  lemma assign_trule: "\<Turnstile>\<^sub>t {\<lambda>z s. P z (s( x := (s x)(aval i s := aval a s) )) } x[i]::=a {P}"
    by (auto)
    
  lemma assign_trule_workaround: (* Workaround to strange unification problem *)
    assumes "\<And>z s. P z (s( x := (s x)(aval i s := aval a s))) = P' z s"
    shows "\<Turnstile>\<^sub>t {P'} Assign x i a {P}"
    using assms
    by (auto)
    

  lemma clear_trule: "\<Turnstile>\<^sub>t {\<lambda>z s. P z (s( x := (\<lambda>_. 0) )) } CLR x {P}"
    by (auto)
    
  lemma basic_seq_trule:
    assumes "\<Turnstile>\<^sub>t {P} c\<^sub>1 {Q}" "\<Turnstile>\<^sub>t {Q} c\<^sub>2 {R}"
    shows "\<Turnstile>\<^sub>t {P} c\<^sub>1;;c\<^sub>2 {R}"
    using assms by force
  
  lemma if_trule:  
    assumes "\<Turnstile>\<^sub>t {P1} c\<^sub>1 {Q}" "\<Turnstile>\<^sub>t {P2} c\<^sub>2 {Q}"
    shows "\<Turnstile>\<^sub>t {\<lambda>z s. COND (bval b s) (P1 z s) (P2 z s)} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"
    using assms unfolding COND_def by force
  
  lemma basic_while_trule:
    assumes WF: "wf R"
    assumes S: "\<Turnstile>\<^sub>t {\<lambda>(z,s\<^sub>0) s. P z s \<and> bval b s \<and> s=s\<^sub>0} c {\<lambda>(z,s\<^sub>0) s. P z s \<and> (s,s\<^sub>0)\<in>R}"
    shows "\<Turnstile>\<^sub>t {P} WHILE b DO c {\<lambda>z s. P z s \<and> \<not> bval b s}"
  proof (rule hoaret_validI)  
    fix z s
    assume I0: "P z s"
    with WF show "\<exists>t. (WHILE b DO c, s) \<Rightarrow> t \<and> P z t \<and> \<not> bval b t"
    proof (induction s rule: wf_induct_rule)
      case (less s)
      show ?case proof (cases "bval b s")
        case True
        with S less.prems obtain s' where "(c,s) \<Rightarrow> s'" "P z s'" "(s',s)\<in>R"
          by auto
        with less.IH obtain t where "(WHILE b DO c, s') \<Rightarrow> t" "P z t" "\<not> bval b t"
          by blast
        with WhileTrue[OF True \<open>(c,s) \<Rightarrow> s'\<close>] show ?thesis by blast
      next  
        case False
        with less.prems show ?thesis by auto
      qed
    qed
  qed
  
  text \<open>We swap the premises of the sequence rule, as our 
    verification condition generator will work on sequences 
    from right to left.\<close>
  lemma seq_trule:
    assumes "\<Turnstile>\<^sub>t {Q} c\<^sub>2 {R}" "\<Turnstile>\<^sub>t {P} c\<^sub>1 {Q}"
    shows "\<Turnstile>\<^sub>t {P} c\<^sub>1;;c\<^sub>2 {R}"
    using basic_seq_trule assms by blast
  
  
  text \<open>We combine the while-rule with a consequence rule, to
    make it more usable in verification condition generation\<close>
  
  (* Explicit backwards derivation *)
  lemma while_trule:
    assumes "wf R"
    assumes "\<Turnstile>\<^sub>t {Ph} c {\<lambda>(z,s\<^sub>0) s. P z s \<and> (s, s\<^sub>0) \<in> R}"
    assumes "\<And>z s. \<lbrakk>P z s; bval b s\<rbrakk> \<Longrightarrow> Ph (z,s) s"
    assumes "\<And>z s. \<lbrakk>P z s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q z s"
    shows "\<Turnstile>\<^sub>t {\<lambda>z. P z} WHILE b DO c {\<lambda>z. Q z}"
    apply (rule conseq_post_trule[where Q="\<lambda>z s. P z s \<and> \<not>bval b s"])
    apply (rule assms; simp)
    apply (rule basic_while_trule)
    apply (rule assms)
    apply (rule conseq_pre_trule)
    apply (rule assms)
    apply clarify
    apply (rule assms; assumption)
    done
    

end


section \<open>Modularity\<close>
subsection \<open>Re-Using already proved specifications\<close>
lemma frame_rule_eq: 
  "\<Turnstile> {P} c {Q} \<longleftrightarrow> (\<forall>R. \<Turnstile> {\<lambda>z s. \<exists>z'. P z' s \<and> (\<forall>t. Q z' t \<longrightarrow> R z t) } c {R})"
  unfolding hoare_valid_def 
  by blast

lemma frame_rule:
  assumes "\<Turnstile> {P} c {Q}"
  shows "\<Turnstile> {\<lambda>z s. \<exists>z'. P z' s \<and> (\<forall>t. Q z' t \<longrightarrow> R z t) } c {R}"
  using assms frame_rule_eq by blast

lemma frame_trule_eq: 
  "\<Turnstile>\<^sub>t {P} c {Q} \<longleftrightarrow> (\<forall>R. \<Turnstile>\<^sub>t {\<lambda>z s. \<exists>z'. P z' s \<and> (\<forall>t. Q z' t \<longrightarrow> R z t) } c {R})"
  unfolding hoaret_valid_def 
  by blast

lemma frame_trule:
  assumes "\<Turnstile>\<^sub>t {P} c {Q}"
  shows "\<Turnstile>\<^sub>t {\<lambda>z s. \<exists>z'. P z' s \<and> (\<forall>t. Q z' t \<longrightarrow> R z t) } c {R}"
  using assms frame_trule_eq by blast
  
subsection \<open>Modified Variables\<close>  

definition eq_on :: "state \<Rightarrow> state \<Rightarrow> vname set \<Rightarrow> bool" ("_ = _ on _" [50,50,50] 50)
  where "s=t on X \<longleftrightarrow> (\<forall>x\<in>X. s x = t x)"
  
lemma eq_on_subst_same[simp]: 
  "x\<in>X \<Longrightarrow> s(x:=v) = t on X \<longleftrightarrow> t x = v \<and> s=t on (X-{x})"  
  "x\<in>X \<Longrightarrow> s = t(x:=v) on X \<longleftrightarrow> s x = v \<and> s=t on (X-{x})"  
  by (auto simp: eq_on_def)
  
lemma eq_on_subst_other[simp]: 
  "x\<notin>X \<Longrightarrow> s(x:=v) = t on X \<longleftrightarrow> s=t on X"
  "x\<notin>X \<Longrightarrow> s = t(x:=v) on X \<longleftrightarrow> s=t on X"
  by (auto simp: eq_on_def)
  
lemma eq_on_refl[simp]: "s = s on X"  
  by (auto simp: eq_on_def)
  
subsubsection \<open>Syntactic Approximation\<close>
fun lhs_vars :: "com \<Rightarrow> vname set" where
  "lhs_vars SKIP = {}"
| "lhs_vars (Clear x) = {x}"  
| "lhs_vars (Assign x _ _) = {x}"
| "lhs_vars (Seq c1 c2) = lhs_vars c1 \<union> lhs_vars c2"
| "lhs_vars (If b c1 c2) = lhs_vars c1 \<union> lhs_vars c2"  
| "lhs_vars (While b c) = lhs_vars c"
  
lemma lhs_vars_sound: "(c,s) \<Rightarrow> t \<Longrightarrow> s = t on -lhs_vars c"
  apply (induction rule: big_step_induct)
  apply (auto simp: eq_on_def)
  done
  

subsubsection \<open>Annotation to Hoare Triple\<close>
  
definition hoaret_mod_valid
  :: "('a \<Rightarrow> assn) \<Rightarrow> com \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> vname set \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)} mod _" [0,0,0,50] 50)
  where "\<Turnstile>\<^sub>t {P} c {Q} mod X \<equiv> \<Turnstile>\<^sub>t {\<lambda>(z,s\<^sub>0) s. P z s \<and> s\<^sub>0=s } c {\<lambda>(z,s\<^sub>0) t. Q z t \<and> s\<^sub>0=t on -X}"

lemma frame_mod_trule:
  assumes "\<Turnstile>\<^sub>t {P} c {Q} mod X"
  shows "\<Turnstile>\<^sub>t {\<lambda>z s. \<exists>z'. P z' s \<and> (\<forall>t. Q z' t \<and> s=t on -X \<longrightarrow> R z t) } c {R}"
  apply (rule conseq_pre_trule)
  apply (rule frame_trule)
  using assms[unfolded hoaret_mod_valid_def] apply assumption
  by auto

text \<open>Annotate Syntactic Approximation\<close>
lemma hoaret_modI:
  assumes "lhs_vars c \<subseteq> X"
  assumes "\<Turnstile>\<^sub>t {P} c {Q}"
  shows "\<Turnstile>\<^sub>t {P} c {Q} mod X"
  using assms
  using lhs_vars_sound
  unfolding hoaret_mod_valid_def hoaret_valid_def eq_on_def apply simp by fast


definition hoare_mod_valid
  :: "('a \<Rightarrow> assn) \<Rightarrow> com \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> vname set \<Rightarrow> bool"
  ("\<Turnstile> {(1_)}/ (_)/ {(1_)} mod _" [0,0,0,50] 50)
  where "\<Turnstile> {P} c {Q} mod X \<equiv> \<Turnstile> {\<lambda>(z,s\<^sub>0) s. P z s \<and> s\<^sub>0=s } c {\<lambda>(z,s\<^sub>0) t. Q z t \<and> s\<^sub>0=t on -X}"

lemma frame_mod_rule:
  assumes "\<Turnstile> {P} c {Q} mod X"
  shows "\<Turnstile> {\<lambda>z s. \<exists>z'. P z' s \<and> (\<forall>t. Q z' t \<and> s=t on -X \<longrightarrow> R z t) } c {R}"
  apply (rule conseq_pre_rule)
  apply (rule frame_rule)
  using assms[unfolded hoare_mod_valid_def] apply assumption
  by auto

text \<open>Annotate Syntactic Approximation\<close>
lemma hoare_modI:
  assumes "lhs_vars c \<subseteq> X"
  assumes "\<Turnstile> {P} c {Q}"
  shows "\<Turnstile> {P} c {Q} mod X"
  using assms
  using lhs_vars_sound
  unfolding hoare_mod_valid_def hoare_valid_def eq_on_def apply simp by fast
  
  
  
section \<open>Verification Condition Generator\<close>

subsection \<open>Simplifier Setup\<close>
  named_theorems vcg_vars_mksimps

  (* TODO: These functions may be of general interest *)
  ML \<open>
    fun eq_classes_witness _ [] = []
      | eq_classes_witness f (x::xs) = let
          val w = f x
          val (this,other) = List.partition (fn y => f y = w) xs
        in
          (w,x::this)::eq_classes_witness f other
        end
  
    fun gen_assoc_map l = eq_classes_witness fst l |> map (apsnd (map snd))
  \<close>
  
  ML \<open>
    
    fun add_vars_mksimps ctxt = let
      
      fun make_pair thm = let
        fun get_cname [Const (@{const_name Trueprop},_)$c] = get_cname [c]
          | get_cname [t$_] = get_cname [t]
          | get_cname [Const (name,_)] = SOME name
          | get_cname _ = NONE
        
      in
        case get_cname (Thm.prems_of thm) of
          SOME n => SOME (n,thm)
        | NONE => (
            warning ("Invalid mksimps_pair thm: " ^ @{make_string} thm); (* TODO: Pretty-print thm! *)
            NONE
        )  
      end
        
      val thms = Named_Theorems.get ctxt @{named_theorems vcg_vars_mksimps}
      val pairs = map_filter make_pair thms |> gen_assoc_map

      val mksimps_pairs = 
        pairs @ mksimps_pairs |> gen_assoc_map |> map (apsnd flat)
      val ctxt = Simplifier.set_mksimps (mksimps mksimps_pairs) ctxt
      
    in 
      ctxt
    end  
      
  \<close>
  
  method_setup vars_clarsimp = \<open>
      Scan.succeed (fn ctxt => SIMPLE_METHOD' (CHANGED_PROP o (
        let
          val ctxt = Splitter.del_split @{thm if_split} ctxt
            delsimps @{thms fun_upd_apply}
            addsimps @{thms fun_upd_same fun_upd_other}
        in
          clarsimp_tac (add_vars_mksimps ctxt)
        end
      )))
  \<close>

subsection \<open>Variable Binding\<close>
  definition vbind :: "vname \<Rightarrow> ('a \<Rightarrow> int \<Rightarrow> val) \<Rightarrow> 'a \<Rightarrow> state \<Rightarrow> bool" where "vbind x ty v s \<equiv> s x = ty v"

  definition VAR_BIND :: "vname \<Rightarrow> _ \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> assn" where
    "VAR_BIND x ty Q s \<equiv> \<exists>v. vbind x ty v s \<and> Q v s"
  definition VAR_CHANGED :: "(int \<Rightarrow> val) \<Rightarrow> ('a \<Rightarrow> int \<Rightarrow> val) \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> assn" where
    "VAR_CHANGED k ty Q s \<equiv> \<exists>v. k = ty v \<and> Q v s"
  
  definition EQ :: "(int \<Rightarrow> val) \<Rightarrow> ('a \<Rightarrow> int \<Rightarrow> val) \<Rightarrow> 'a \<Rightarrow> bool" where
    "EQ k ty v \<equiv> k = ty v"
    
  definition VAR_BIND_FINAL :: "bool \<Rightarrow> assn" where "VAR_BIND_FINAL x _ = x"
    (* Required for protection against eta-contraction on printing, 
      and ensuring that final predicate does not depend on state *)

  text \<open>Variable bindings in assumptions\<close>
  
  lemma imapD[vcg_vars_mksimps]: "vbind x ty a s \<Longrightarrow> s x = ty a" by (auto simp: vbind_def)
  
  lemma eq_onD[vcg_vars_mksimps]: "a=b on X \<Longrightarrow> \<forall>x\<in>X. a x = b x"  
    by (auto simp: eq_on_def)
  
  lemma eq_onD2[vcg_vars_mksimps]: "a=b on X \<Longrightarrow> \<forall>x\<in>X. vbind x ty v a = vbind x ty v b"  
    by (auto simp: eq_on_def vbind_def)
    
  
  
  lemma imap_subst[simp]: 
    "x\<noteq>y \<Longrightarrow> vbind x ty v (s(y:=b)) \<longleftrightarrow> vbind x ty v s"
    "vbind x ty v (s(x:=b)) \<longleftrightarrow> b = ty v"
    unfolding vbind_def by auto

  lemma VAR_BIND_elim:
    assumes "VAR_BIND x ty (\<lambda>v. Q v) s"
    obtains v where "vbind x ty v s" "Q v s"
    using assms unfolding VAR_BIND_def by auto

  lemma VAR_BIND_FINAL_elim: 
    assumes "VAR_BIND_FINAL Q s"
    obtains Q using assms unfolding VAR_BIND_FINAL_def by auto
    
  lemmas VAR_BIND_elims = VAR_BIND_FINAL_elim VAR_BIND_elim
    
  text \<open>Variable Bindings in Conclusion\<close>
  text \<open>Handle substitutions\<close>
  
  lemma var_bind_simp1: "x\<noteq>y \<Longrightarrow> VAR_BIND x ty Q (s(y:=v)) \<longleftrightarrow> VAR_BIND x ty (\<lambda>w s. Q w (s(y:=v))) s"
    unfolding VAR_BIND_def vbind_def by auto
  
  lemma var_bind_simp2: "VAR_BIND x ty Q (s(x:=v)) \<longleftrightarrow> VAR_CHANGED v ty (\<lambda>w s. Q w (s(x:=v))) s"  
    unfolding VAR_BIND_def VAR_CHANGED_def vbind_def by auto

  lemma var_bind_simp3: "VAR_CHANGED k ty Q (s(x:=v)) \<longleftrightarrow> VAR_CHANGED k ty (\<lambda>w s. Q w (s(x:=v))) s"
    unfolding VAR_CHANGED_def by auto
    
  lemma var_bind_simp4: "VAR_BIND_FINAL Q (s(x:=v)) = VAR_BIND_FINAL Q s"
    by (auto simp: VAR_BIND_FINAL_def)

  lemmas var_bind_simps = var_bind_simp1 var_bind_simp2 var_bind_simp3 
    var_bind_simp4
    
  text \<open>Resolve Conditionals\<close>
  lemma CONDI: 
    assumes "b \<Longrightarrow> P" "\<not>b \<Longrightarrow> Q"
    shows "COND b P Q"
    using assms by (auto simp: COND_def)
  
    
  text \<open>Instantiate\<close>
    
  lemma VAR_BINDI: 
    assumes "vbind x ty v s" "Q v s"
    shows "VAR_BIND x ty Q s"
    using assms
    unfolding VAR_BIND_def VAR_CHANGED_def by auto
  
  lemma VAR_CHANGEDI:  
    assumes "EQ k ty v" "Q v s"
    shows "VAR_CHANGED k ty Q s"
    using assms
    unfolding VAR_CHANGED_def EQ_def by auto
    
  lemma VAR_BIND_FINALI: 
    assumes "Q"
    shows "VAR_BIND_FINAL Q s"
    using assms
    by (auto simp: VAR_BIND_FINAL_def)
    
  lemma EQIs:
    "EQ a imap a"
    "EQ (ty v) ty v"
    unfolding EQ_def by auto
  
  method vcg_resolve_binding =  
    rule VAR_BINDI, assumption
  | rule VAR_CHANGEDI, rule EQIs
  
  method vcg_try_resolve_bindings =
    (imp_basic_simp add: var_bind_simps)?;
    (vcg_resolve_binding+)?
  
  method vcg_resolve_bindings = match conclusion in 
    "VAR_BIND _ _ _ _" \<Rightarrow> \<open>vcg_try_resolve_bindings; (rule VAR_BIND_FINALI)\<close>
  \<bar> _ \<Rightarrow> succeed
    
    
subsubsection \<open>Syntax\<close>



(*
(* TODO: How to activate this syntax only in bundle? *)
nonterminal var_bind and var_binds


syntax
  "_var_block" :: "var_binds \<Rightarrow> 'a" ("vars _" [12] 10)
  "_var_final" :: "var_bind \<Rightarrow> 'a \<Rightarrow> var_binds" ("_ in _" [13,12] 12)
  "_var_cons" :: "var_bind \<Rightarrow> var_binds \<Rightarrow> var_binds" ("_/ _" [13,12] 12)
  "_var_bind_nvt" :: "'a \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> var_bind" ("'(_ as _ : _')" [14,14,14] 14)
  "_var_bind_nt" :: "idt \<Rightarrow> 'a \<Rightarrow> var_bind" ("'(_ : _')" [14,14] 14)
  "_var_bind_nv" :: "'a \<Rightarrow> idt \<Rightarrow> var_bind" ("'(_ as _')" [14,14] 14)
  "_var_bind_n" :: "idt \<Rightarrow> var_bind" ("_" [14] 14)
  
syntax 
  "_var_app" :: "var_bind \<Rightarrow> 'a \<Rightarrow> 'a" 
  "_var_bind_s" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  
translations
  "_var_block (_var_final b Q)" \<rightleftharpoons> "_var_app b (CONST VAR_BIND_FINAL Q)"
  "_var_block (_var_cons b bs)" \<rightleftharpoons> "_var_app b (_var_block bs)"
  "_var_app (_var_bind_nvt x v ty) bs" \<rightleftharpoons> "_var_bind_s x ty (\<lambda>v. bs)"
  "_var_bind_nv x v" \<rightleftharpoons> "_var_bind_nvt x v (CONST var)"
  "_var_bind_nt x ty" \<rightharpoonup> "_var_bind_nvt (x) x ty"
  "_var_bind_n x" \<rightharpoonup> "_var_bind_nv (x) x"
  "_var_cons b c" \<leftharpoondown>  "_var_final b (_var_block c)"
  
  
*)  

(*syntax
  "_var_block" :: "var_binds \<Rightarrow> 'a" ("vars _" [12] 10)
  "_var_final" :: "var_bind \<Rightarrow> 'a \<Rightarrow> var_binds" ("_ in _" [13,12] 12)
  "_var_cons" :: "var_bind \<Rightarrow> var_binds \<Rightarrow> var_binds" ("_,/ _" [13,12] 12)
  "_var_bind_nvt" :: "'a \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> var_bind" ("_ as _ : _" [14,14,14] 14)
  "_var_bind_nt" :: "idt \<Rightarrow> 'a \<Rightarrow> var_bind" ("_ : _" [14,14] 14)
  "_var_bind_nv" :: "'a \<Rightarrow> idt \<Rightarrow> var_bind" ("_ as _" [14,14] 14)
  "_var_bind_n" :: "idt \<Rightarrow> var_bind" ("_" [14] 14)
*)

(* TODO: How to activate this syntax only in bundle? *)
nonterminal var_bind and var_binds

syntax 
  "_var_blockf" :: "var_binds \<Rightarrow> 'a \<Rightarrow> 'a" ("vars _ in _" [12,12] 10)
  "_var_block" :: "var_binds \<Rightarrow> 'a \<Rightarrow> 'a"
  "_var_final" :: "var_bind \<Rightarrow> var_binds" ("_" [13] 12)
  "_var_cons" :: "var_bind \<Rightarrow> var_binds \<Rightarrow> var_binds" ("_/ _" [13,12] 12)
  "_var_bind_nvt" :: "'a \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> var_bind" ("'(_ as _ : _')" [14,14,14] 14)
  "_var_bind_nt" :: "idt \<Rightarrow> 'a \<Rightarrow> var_bind" ("'(_ : _')" [14,14] 14)
  "_var_bind_nv" :: "'a \<Rightarrow> idt \<Rightarrow> var_bind" ("'(_ as _')" [14,14] 14)
  "_var_bind_n" :: "idt \<Rightarrow> var_bind" ("_" [14] 14)

(* Syntax to output odd var-bindings, which can occur for partially unfolded var-binding blocks *)
syntax (output)   
  "_var_block" :: "var_binds \<Rightarrow> 'a \<Rightarrow> 'a" ("var\<^sub>n\<^sub>o\<^sub>f\<^sub>i\<^sub>n\<^sub>a\<^sub>l _ in/ _")
  
syntax 
  "_var_bind_s" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  
translations  
  "_var_blockf bs P" \<rightleftharpoons> "_var_block bs (CONST VAR_BIND_FINAL P)"
  "_var_block (_var_cons (_var_bind_nvt x v ty) bs) P" \<rightleftharpoons> "_var_bind_s x ty (\<lambda>v. _var_block bs P)"
  "_var_block (_var_final (_var_bind_nvt x v ty)) P" \<rightleftharpoons> "_var_bind_s x ty (\<lambda>v. P)"
  "s" \<leftharpoondown> "_var_final s"
  "_var_blockf (_var_cons b c) P" \<leftharpoondown> "_var_block b (_var_blockf c P)"

translations
  "_var_bind_nv x v" \<rightleftharpoons> "_var_bind_nvt x v (CONST var)"
  "_var_bind_nt x ty" \<rightharpoonup> "_var_bind_nvt (x) x ty"
  "_var_bind_n x" \<rightharpoonup> "_var_bind_nv (x) x"

ML \<open>
  local
    open IMP_Translation
  in
    fun xform_var_arg (Const (@{syntax_const "_constrain"}, _) $ t $ _) = xform_var_arg t
      | xform_var_arg (Free (str,_)) = SOME (HOLogic.mk_string str)
      | xform_var_arg _ = NONE

    fun 
      var_bind_s_tr _ [x, ty, q] = let
        val x = the_default x (xform_var_arg x)
      in
        Syntax.const @{const_name VAR_BIND}$x$ty$q
      end
    | var_bind_s_tr _ ts = raise (TERM ("var_bind_s_tr",ts))
      
  
    fun
      var_bind_s_tr' _ (x::ts) = let
        val x = case try dest_var_syntax x of
          NONE => x
        | SOME s => Syntax.const s  
      
      in
        list_comb (Syntax.const @{syntax_const "_var_bind_s"}, x::ts)
      end
    | var_bind_s_tr' _ _ = raise Match
    
    fun bound_eq (Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, x, _]) y = bound_eq x y
      | bound_eq (Ast.Appl [Ast.Constant @{syntax_const "_bound"}, x]) y = bound_eq x y
      | bound_eq (Ast.Variable x) y = x = y
      | bound_eq _ _ = false
    
    fun var_same_ast_tr' [(Ast.Constant x), b] = 
      if bound_eq b x then
        Ast.Appl [Ast.Constant @{syntax_const "_var_bind_n"}, b]
      else raise Match
    | var_same_ast_tr' [(Ast.Constant x), b, ty] = 
      if bound_eq b x then
        Ast.Appl [Ast.Constant @{syntax_const "_var_bind_nt"}, b, ty]
      else raise Match
    | var_same_ast_tr' _ = raise Match  
    
    val setup = 
      Sign.parse_translation [
          (@{syntax_const "_var_bind_s"}, var_bind_s_tr)
        ]
      #>
      Sign.print_translation [
        (@{const_syntax VAR_BIND}, var_bind_s_tr')
      ]
      #>
    Sign.print_ast_translation
     [(@{syntax_const "_var_bind_nvt"}, K var_same_ast_tr'),
      (@{syntax_const "_var_bind_nv"}, K var_same_ast_tr')
     ];
      
    val _ = Theory.setup setup
      
  end
\<close>

lemma "(vars a b c in P a b c) s"
  unfolding VAR_BIND_FINAL_def
  oops

lemma "XP (vars a (b : var) c (x as xx) (''xx.d'' as xxx) (''__y'' as yy : id) in P a b c)"
  unfolding VAR_BIND_FINAL_def 
  oops

 
subsection \<open>Annotating While Loops\<close>
definition AWHILE :: "('a \<Rightarrow> assn) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" ("(INVAR (_)/ WHILE (\<open>unbreakable\<close>_) DO(2/ _))"  [0, 0, 61] 61)
  where "INVAR I WHILE b DO c \<equiv> WHILE b DO c"

lemma annot_invar: "(WHILE b DO c) = (INVAR I WHILE b DO c)" by (simp add: AWHILE_def)
  
lemma awhile_rule:
  assumes "\<Turnstile> {R} c {P}"
  assumes "\<And>z s. \<lbrakk>P z s; bval b s\<rbrakk> \<Longrightarrow> R z s"
  assumes "\<And>z s. \<lbrakk>P z s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q z s"
  shows "\<Turnstile> {P} INVAR P WHILE b DO c {Q}"
  unfolding AWHILE_def by (rule while_rule[OF assms])

definition AWHILET :: "(state\<times>state) set \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" ("(VAR (_)/ INVAR (_)/ WHILE (\<open>unbreakable\<close>_) DO(2/ _))"  [0, 0, 0, 61] 61)
  where "VAR R INVAR I WHILE b DO c \<equiv> WHILE b DO c"

lemma annot_tinvar: "(WHILE b DO c) = (VAR R INVAR I WHILE b DO c)" by (simp add: AWHILET_def)
  
lemma awhile_trule:
  fixes R :: "(state \<times> state) set"
  assumes "wf R"
  assumes "\<Turnstile>\<^sub>t {Ph} c {\<lambda>(z,s\<^sub>0) s. P z s \<and> (s, s\<^sub>0) \<in> R}"
  assumes "\<And>z s. \<lbrakk>P z s; bval b s\<rbrakk> \<Longrightarrow> id Ph (z,s) s"
  assumes "\<And>z s. \<lbrakk>P z s; \<not>bval b s\<rbrakk> \<Longrightarrow> Q z s"
  shows "\<Turnstile>\<^sub>t {\<lambda>z. P z} VAR R INVAR P WHILE b DO c {\<lambda>z. Q z}"
  unfolding AWHILET_def
  by (rule while_trule[OF assms[simplified]])
  
lemma lhs_vars_awhile[simp]:
  "lhs_vars (INVAR I WHILE b DO c) = lhs_vars c"
  "lhs_vars (VAR R INVAR I WHILE b DO c) = lhs_vars c"
  unfolding AWHILE_def AWHILET_def by auto
  
  
  
text \<open>Measure function by aexp\<close>
abbreviation "measure_exp a \<equiv> measure (nat o aval a)"
  
  
subsection \<open>Basic VCG\<close>  

named_theorems vcg_rules

lemmas [vcg_rules] =
  skip_rule assign_rule clear_rule seq_rule if_rule awhile_rule
  skip_trule assign_trule clear_trule seq_trule if_trule awhile_trule conjI

named_theorems vcg_init_rules  
lemmas [vcg_init_rules] = conseq_pre_rule conseq_pre_trule
  
method vcg_is_no_hoare_triple = match conclusion in 
    "\<Turnstile> {_} _ {_}" \<Rightarrow> fail 
  \<bar> "\<Turnstile>\<^sub>t {_} _ {_}" \<Rightarrow> fail 
  \<bar> _ \<Rightarrow> succeed

definition VERIFICATION_CONDITION :: "bool \<Rightarrow> bool" where
  "VERIFICATION_CONDITION P = P"

lemma VC_I: "P \<Longrightarrow> VERIFICATION_CONDITION P" by (simp add: VERIFICATION_CONDITION_def)
lemma VC_D: "VERIFICATION_CONDITION P \<Longrightarrow> P" by (simp add: VERIFICATION_CONDITION_def)

method vcg_rule_wrapper methods m = m; (vcg_is_no_hoare_triple, rule VC_D)?

method vcg_rule (* Apply Hoare-rule and tag side conditions *)
  = vcg_rule_wrapper\<open>rule vcg_rules | rule frame_mod_rule frame_mod_trule, rule vcg_rules\<close>

lemma redundant_vbindE:
  assumes "vbind x ty v1 s" "vbind x ty v2 s"
  obtains "ty v1 = ty v2"
  using assms by (auto simp: vbind_def)
  
method_setup vcg_redundant_vbind = \<open>
 Scan.succeed (fn ctxt => SIMPLE_METHOD (
   REPEAT_DETERM1 (FIRSTGOAL (EVERY' [eresolve_tac ctxt @{thms redundant_vbindE}, assume_tac ctxt]))
 ))\<close>
  
  
method vcg_prepare_goal -- \<open>Applied before processing any goal\<close>
  = (elim VAR_BIND_elims conjE)?;((vars_clarsimp| vcg_redundant_vbind)+)?
  
lemma thin_imap: "vbind x ty v s \<Longrightarrow> P \<Longrightarrow> P" .
lemma thin_eqon: "s = t on X \<Longrightarrow> P \<Longrightarrow> P" .
  
method_setup vcg_remove_binding_assms = \<open>
 Scan.succeed (fn ctxt => SIMPLE_METHOD (
   REPEAT_DETERM (FIRSTGOAL (eresolve_tac ctxt @{thms thin_imap thin_eqon}))
 ))\<close>

(*method vcg_remove_binding_assms = ((thin_tac "imap _ _ _ _")+)?*)

definition "MOD_VAR_APPROX A B \<equiv> A\<subseteq>B"
lemma MOD_VAR_APPROXI: "A\<subseteq>B \<Longrightarrow> MOD_VAR_APPROX A B"
  by (auto simp: MOD_VAR_APPROX_def)

lemma hoaret_modI_vcg:
  assumes "MOD_VAR_APPROX (lhs_vars c) X"
  assumes "\<Turnstile>\<^sub>t {P} c {Q}"
  shows "\<Turnstile>\<^sub>t {P} c {Q} mod X"
  using assms hoaret_modI unfolding MOD_VAR_APPROX_def by blast

lemma hoare_modI_vcg:
  assumes "MOD_VAR_APPROX (lhs_vars c) X"
  assumes "\<Turnstile> {P} c {Q}"
  shows "\<Turnstile> {P} c {Q} mod X"
  using assms hoare_modI unfolding MOD_VAR_APPROX_def by blast
  
lemmas [vcg_init_rules] = 
  hoaret_modI_vcg[OF _ conseq_pre_trule]  
  hoare_modI_vcg[OF _ conseq_pre_rule]  
    
  
method solve_mod_var_approx = (rule MOD_VAR_APPROXI; auto; fail)



definition "INST_VARS X \<equiv> True"

lemma INST_VARS_I:
  "INST_VARS P \<Longrightarrow> INST_VARS Q \<Longrightarrow> INST_VARS (P\<and>Q)"
  "INST_VARS (x = x)"
  by (auto simp add: INST_VARS_def)  

lemma INST_VARS_rem: "INST_VARS X" by (auto simp add: INST_VARS_def)  

lemma INST_VARS_begin:
  "INST_VARS P \<Longrightarrow> P \<Longrightarrow> P" .

method vcg_inst_vars =
    rule INST_VARS_begin,
    (((rule INST_VARS_I | rule INST_VARS_rem)+) [])


method vcg_prepare_vc -- \<open>Applied to prepare verification condition. May solve it.\<close>
  = rule VC_I;(intro conjI impI allI CONDI exI)?;vcg_prepare_goal; (vcg_resolve_bindings; vcg_remove_binding_assms | vcg_try_resolve_bindings); vcg_inst_vars

method vcgdbg_prepare_vc -- \<open>Applied to prepare verification condition. May solve it.\<close>
  = rule VC_I;(intro conjI impI allI CONDI exI)?;vcg_prepare_goal; (vcg_resolve_bindings | vcg_try_resolve_bindings); vcg_inst_vars
  
method vcg_step_solver methods solver 
  = vcg_prepare_goal; ( vcg_rule | vcg_prepare_vc;solver )
method vcg_default_solver = clarsimp?; (safe?;clarsimp?;simp?;solve_mod_var_approx?;fail)?

method vcgdbg_step_solver methods solver 
  = vcg_prepare_goal; ( vcg_rule | vcgdbg_prepare_vc;solver )

method vcg_step = vcg_step_solver\<open>vcg_default_solver\<close>
method vcg_ctd = (vcg_step)+

method vcgdbg_step = vcgdbg_step_solver\<open>vcg_default_solver\<close>
method vcgdbg_ctd = (vcgdbg_step)+

method vcg_init = vcg_rule_wrapper\<open>rule vcg_init_rules\<close>

method vcg = vcg_init, vcg_ctd

method vcg_ctd_raw = (vcg_step_solver\<open>succeed\<close>)+
method vcg_raw = vcg_init, vcg_ctd_raw
  

subsection \<open>Deferred VCs\<close>  

definition DEFERRED :: "bool \<Rightarrow> bool" where "DEFERRED P = P"
lemma DEFERREDD: "DEFERRED P \<Longrightarrow> P" by (auto simp: DEFERRED_def)

method vcg_can_defer =
  (
    match conclusion 
      in "DEFERRED _" \<Rightarrow> fail -- \<open>Refuse to defer already deferred goals\<close>
    \<bar> "\<Turnstile> {_} _ {_}" \<Rightarrow> fail  -- \<open>Refuse to defer Hoare triples (They are no VCs!)\<close>
    \<bar> "\<Turnstile>\<^sub>t {_} _ {_}" \<Rightarrow> fail  -- \<open>Refuse to defer Hoare triples (They are no VCs!)\<close>
    \<bar> _ \<Rightarrow> succeed)

method vcg_defer = 
  vcg_can_defer, rule DEFERREDD, tactic \<open>FIRSTGOAL defer_tac\<close>

method vcg_all =  
  (vcg_init, (vcg_ctd, vcg_defer? | vcg_defer)+, (unfold DEFERRED_def)?)


end
