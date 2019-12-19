theory Base

imports Main

begin

definition
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_, _:_" [90, 0, 0] 91) where
  "\<Gamma>, i:a = (\<lambda>j. if j < i then \<Gamma> j else if j = i then a else \<Gamma> (j - 1))"

text \<open>
lemma shift_eq [simp]: "i = j \<Longrightarrow> (\<Gamma>, i:T) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (\<Gamma>, i:T) j = \<Gamma> j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (\<Gamma>, i:T) j = \<Gamma> (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "\<Gamma>, i:U, 0:T = \<Gamma>, 0:T, Suc i:U"
  by (rule ext) (simp_all add: shift_def split: nat.split)
\<close>

type_synonym varName = nat
type_synonym typeName = nat

datatype "type" =
	Atom typeName
	| Fun type type (infixr "->" 200)

type_synonym varCtx = "varName => type"


datatype "term" =
	Var "varName"
	| Abs varName "type" "term"
	| App "term" "term" (infixl "\<degree>" 200)

inductive "value" :: "term => bool" where
	"value (Abstraction _ _ _)"

primrec
  substn :: "[term, term, nat] => term"
where
    "substn (Var i) s k =
      (if k < i then Var (i - 1) else if i = k then liftn k s 0 else Var i)"
  | "substn (t ° u) s k = substn t s k ° substn u s k"
  | "substn (Abs k T t) s k = Abs (substn t s (k + 1))"

text \<open> TODO: Add value requirements\<close>
inductive "evaluation" :: "[term, term] \<Rightarrow> bool" (infixl "\<rightarrow>" 50)
  where
    e_app_1: "t1 \<rightarrow> t1' \<Longrightarrow> t1 \<degree> t2 \<rightarrow> t1' \<degree> t2"
    e_app_2: "t2 \<rightarrow> t2' \<Longrightarrow> t1 \<degree> t2 \<rightarrow> t1 \<degree> t2'"
    e_app_abs: "Abs x T t"


inductive
	typing :: "varCtx => term => type => bool" ("_ ⊢ _ : _" [50, 50, 50] 50)

	where

	t_abs : "\<Gamma>, x:T1 ⊢ t2 : T2 ==> \<Gamma> ⊢ Abs x T1 t : (T1 -> T2)"
	| t_var : "\<Gamma>(x) = T ==> \<Gamma> ⊢ (Var x) : T"
	| t_app : "\<Gamma> ⊢ t1 : (T1 -> T2) ==> \<Gamma> ⊢ t2 : T1 ==> \<Gamma>  ⊢ (t1 \<degree> t2) : T2"

inductive_cases typing_elims [elim!]:
  "\<Gamma> ⊢ Var x : T"
  "\<Gamma> ⊢ t \<degree> u : T"
  "\<Gamma> ⊢ Abs x T1 t : T"

