theory Base

imports Main

begin

type_synonym varName = nat
type_synonym typeName = nat

datatype "type" =
	Atom typeName
	| Arrow type type (infixr "->" 200)
	| Unit

type_synonym varCtx = "varName => type"


datatype "term" =
      var "varName"
      | abs varName "type" "term"
      | app "term" "term"
      | unit


definition
  shift :: "(varName \<Rightarrow> 'a) \<Rightarrow> varName \<Rightarrow> 'a \<Rightarrow> varName \<Rightarrow> 'a"  ("_, <_:_>" [90, 0, 0] 91) where
  "\<Gamma>, <i:a> = (\<lambda>j. if j < i then \<Gamma> j else if j = i then a else \<Gamma> (j - 1))"

lemma shift_eq [simp]: "i = j \<Longrightarrow> (\<Gamma>, <i:T>) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (\<Gamma>, <i:T>) j = \<Gamma> j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (\<Gamma>, <i:T>) j = \<Gamma> (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "\<Gamma>, <i:U>, <0:T> = \<Gamma>, <0:T>, <Suc i:U>"
  by (rule ext) (simp_all add: shift_def split: nat.split)

primrec
  lift :: "[term, varName] => term"
where
    "lift (var i) x = (if i < x then var i else var (i + 1))"
  | "lift (app s t) x = app (lift s x) (lift t x)"
  | "lift (abs x T s) y = abs x T (lift s (y + 1))"
  | "lift unit x = unit"

primrec subst_term :: "[term, varName, term] => term" ("_[_ ~> _]" [300, 0, 0] 300)
	where
	subst_var: "(var x)[y ~> t] = (if x = y then t else if x < y then var x else var (x - 1))"
	| subst_app: "(app t1 t2)[y ~> t] = app (t1[y ~> t]) (t2[y ~> t])"
	| subst_abs: "(abs x T1 t1)[y ~> t] = abs x T1 (t1[y + 1 ~> lift t 0])"
	| subst_unit: "unit[y ~> t] = unit"

inductive "value" :: "term => bool"
  where
      val_abs: "value (abs _ _ _)"
      | val_unit: "value unit"

(*
primrec liftn :: "[nat, term, nat] => term"
  where
    "liftn n (var i) k = (if i < k then var i else var (i + n))"
  | "liftn n (app s t) k = app (liftn n s k) (liftn n t k)"
  | "liftn n (abs x T s) k = abs x T (liftn n s (k + 1))"
  | "liftn n unit k = unit"

primrec substn :: "[term, term, nat] => term"
  where
    "substn (var i) s k =
      (if k < i then var (i - 1) else if i = k then liftn k s 0 else var i)"
  | "substn (app t u) s k = app (substn t s k) (substn u s k)"
  | "substn (abs x T t) s k = substn t s (k + 1)"
  | "substn unit s k = unit"
*)

inductive "evaluation" :: "[term, term] \<Rightarrow> bool" (infixl "\<rightarrow>" 50)
  where
    e_app_1: "t1 \<rightarrow> t1' \<Longrightarrow> app t1 t2 \<rightarrow> app t1' t2"
  | e_app_2: "t2 \<rightarrow> t2' \<Longrightarrow> app t1 t2 \<rightarrow> app t1 t2'"
  | e_app_abs: "value t2 \<Longrightarrow> app (abs x T t) t2 \<rightarrow> (substn t t2 x)"


inductive typing :: "varCtx => term => type => bool" ("_ ⊢ _ : _" [50, 50, 50] 50)
  where
    t_abs [intro!]: "\<Gamma>, <x:T1> ⊢ t2 : T2 ==> \<Gamma> ⊢ abs x T1 t2 : (T1 -> T2)"
  | t_var [intro!]: "\<Gamma>(x) = T ==> \<Gamma> ⊢ var x : T"
  | t_app [intro!]: "\<Gamma> ⊢ t1 : (T1 -> T2) ==> \<Gamma> ⊢ t2 : T1 ==> \<Gamma>  ⊢ app t1 t2 : T2"
  | t_unit [intro!]: "\<Gamma> ⊢ unit : Unit"

inductive_cases typing_elims [elim!]:
  "\<Gamma> ⊢ var x : T"
  "\<Gamma> ⊢ app t u : T"
  "\<Gamma> ⊢ abs x T1 t : T"
  "\<Gamma> ⊢ unit : Unit"

schematic_goal "\<Gamma> ⊢ app (abs x Unit (var x)) unit : ?T"
	by force

lemma subst_eq [simp]: "(var x)[x ~> t] = t"
  by (simp add: subst_var)

lemma subst_gt [simp]: "y < x ==> (var x)[y ~> t] = var (x - 1)"
  by (simp add: subst_var)

lemma subst_lt [simp]: "y > x ==> (var x)[y ~> t] = var x"
  by (simp add: subst_var)

lemma canonical_forms_abs:
  fixes t :: "term"
	assumes d: "\<Gamma> ⊢ t : (T1 -> T2)"
		and v: "value t"
	shows "∃ x T1 t2 .t = abs x T1 t2"
  using d typing.cases v value.simps by blast

lemma canonical_forms_unit:
	fixes t :: "term"
	assumes d: "\<Gamma> ⊢ t : Unit"
	  and v: "value t"
	shows "t = unit" using d v value.simps by auto

theorem progress:
	assumes d: "\<Gamma> ⊢ t : T"
	shows "(value t) | (t \<rightarrow> t')"
	sorry

lemma subst_lemma:
	assumes d1: "\<Gamma>, <x:T2> ⊢ t1 : T1"
		and d2: "\<Gamma> ⊢ t2 : T2"
	shows "\<Gamma> ⊢ t1[x ~> t2] : T1"
	sorry

theorem preservation:
	assumes d: "\<Gamma> ⊢ t : T"
		and e: "t \<rightarrow> t'"
	shows "\<Gamma> ⊢ t' : T"
	sorry
