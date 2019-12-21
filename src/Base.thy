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
  shift :: "(varName \<Rightarrow> 'a) \<Rightarrow> varName \<Rightarrow> 'a \<Rightarrow> varName \<Rightarrow> 'a"  ("_, <_:_>" [90, 0, 0] 91)
    where
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

inductive "evaluation" :: "[term, term] \<Rightarrow> bool" (infixl "\<rightarrow>" 50)
  where
    e_app_1: "t1 \<rightarrow> t1' \<Longrightarrow> app t1 t2 \<rightarrow> app t1' t2"
  | e_app_2: "value t1 \<Longrightarrow> t2 \<rightarrow> t2' \<Longrightarrow> app t1 t2 \<rightarrow> app t1 t2'"
  | e_app_abs: "value t2 \<Longrightarrow> app (abs x T t) t2 \<rightarrow> (t[x ~> t2])"


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

lemma canonical_forms_abs [simp]:
  fixes t :: "term"
	assumes d: "\<Gamma> ⊢ t : (T1 -> T2)"
		and v: "value t"
	shows "∃ x T1 t2 .t = abs x T1 t2"
  using d typing.cases v value.simps by blast

lemma canonical_forms_unit [simp]:
	fixes t :: "term"
	assumes d: "\<Gamma> ⊢ t : Unit"
	  and v: "value t"
	shows "t = unit" using d v value.simps by auto

theorem progress:
  fixes t :: "term"
  fixes t' :: "term"
  fixes T :: "type"
	assumes d: "\<Gamma> ⊢ t : T"
  assumes empty_context: "\<forall> x T . \<Gamma>(x) \<noteq> T"
	shows "(value t) | (\<exists> t' . t \<rightarrow> t')"
	using d
  proof induction
    case (t_abs Γ x T1 t2 T2)
    then show ?case
      by (simp add: value.simps)
  next
    case (t_var Γ x T)
    from this empty_context show ?case
      by blast
  next
    case (t_app Γ t1 T1 T2 t2)
    then obtain t1' t2' where
        pt1: "Γ ⊢ t1 : T1 -> T2"
        and pt2: "Γ ⊢ t2 : T1"
        and t1ih: "value t1 ∨ t1 → t1'"
        and t2ih: "value t2 ∨ t2 → t2'"
      by auto
    from t1ih show ?case
    proof
      assume t1v: "value t1"
      from t2ih show ?case
      proof
        assume t2v: "value t2"
        then obtain x T3 t3 where
          t1_abs: "t1 = abs x T3 t3"
          using canonical_forms_abs pt1 t1v by blast
        then have "app (abs x T3 t3) t2 \<rightarrow> t3[x ~> t2]"  by (simp add: e_app_abs t2v t1_abs)
        show ?case
          using ‹app (term.abs x T3 t3) t2 → t3[x ~> t2]› t1_abs by blast
      next
        assume t2e: "t2 \<rightarrow> t2'"
        have te: "app t1 t2 \<rightarrow> app t1 t2'"
          by (simp add: e_app_2 t1v t2e)
        from te show ?case by auto
      qed
    next
      assume t1e: "t1 \<rightarrow> t1'"
      have te: "app t1 t2 \<rightarrow> app t1' t2"
        by (simp add: e_app_1 t1e)
      then show ?case by auto
    qed
  next
    case (t_unit Γ)
    then show ?case by (simp add: value.simps)
qed

lemma subst_lemma:
  fixes t1 :: "term"
  fixes t2 :: "term"
  fixes T1 :: "type"
  fixes T2 :: "type"
	assumes d1: "\<Gamma>, <x:T2> ⊢ t1 : T1"
		and d2: "\<Gamma> ⊢ t2 : T2"
	shows "\<Gamma> ⊢ t1[x ~> t2] : T1"
	using d1 d2
  proof induction
    case (t_abs Γ x T1 t2 T2)
    then obtain t2 T2 where
      "Γ, <x:T1> ⊢ t2 : T2"
      and "Γ ⊢ t2 : T2 ⟹ Γ ⊢ t2[x ~> t2] : T2"
      and "Γ ⊢ t2 : T2"
      by force

    then show ?case sorry
  next
    case (t_var Γ x T)
    then show ?case
      sorry
  next
    case (t_app Γ t1 T1 T2 t2)
    then show ?case
      by auto
  next
    case (t_unit Γ)
    then show ?case by auto
  qed

theorem preservation:
	assumes d: "\<Gamma> ⊢ t : T"
		and e: "t \<rightarrow> t'"
	shows "\<Gamma> ⊢ t' : T"
	using d e
  proof induction
    case (t_abs Γ x T1 t2 T2)
    then show ?case
    using evaluation.cases by blast
  next
    case (t_var Γ x T)
    then show ?case
      using evaluation.cases by blast
  next
    case (t_app Γ t1 T1 T2 t2)
    then obtain t1' t2' where
      p1: "Γ ⊢ t1 : T1 -> T2"
      and p2: "Γ ⊢ t2 : T1"
      and dih1: "t1 → t1' ==> Γ ⊢ t1' : T1 -> T2"
      and dih2: "t2 → t2' ⟹ Γ ⊢ t2' : T1"
      and de: "app t1 t2 \<rightarrow> t'"
      by auto
    from de dih1 dih2 show ?case
    proof cases
      case (e_app_1 t1')
      from this have "app t1 t2 \<rightarrow> app t1' t2"
        using t_app.prems by blast
      from this have "t1 \<rightarrow> t1'"
        using local.e_app_1(2) by blast
      from this dih1 have "Γ ⊢ t1' : T1 -> T2" sorry
      from this show ?thesis
        using local.e_app_1(1) p2 by blast
    next
        case (e_app_2 t2')
        from this have "app t1 t2 \<rightarrow> app t1 t2'"
          using t_app.prems by blast
        from this have "t2 \<rightarrow> t2'"
          by (simp add: local.e_app_2(3))
        from this dih2 have "Γ ⊢ t2' : T1"  sorry
        from this show ?thesis
          using local.e_app_2(1) p1 by blast
    next
        case (e_app_abs x T t)
        from this have "app t1 t2 \<rightarrow> t[x ~> t2]"
          using t_app.prems by blast
      then show ?thesis
        using local.e_app_abs(1) local.e_app_abs(2) p1 p2 subst_lemma by blast
    qed 
  next
    case (t_unit Γ)
    then show ?case
      using evaluation.cases by blast
  qed

