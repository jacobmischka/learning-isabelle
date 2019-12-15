theory Base

imports Main

begin

fun add :: "nat => nat => nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02: "add n 0 = n"
	apply (induction n)
	apply (auto)
	done

end

type_synonym varName = nat
type_synonym typeName = nat

type_synonym varCtx = "varName \<rightharpoonup> typeName"

consts fn

datatype "term" =
	Abstraction x::varName "typeName" t::"term"
	| Var "varName"
	| Application "exp exp"

inductive "value" :: "term => bool" where
	"value (Abstraction _ _ _)"

consts
	typing :: (varCtx * exp * typeName) set

inductive
	typing :: [varCtx, exp, typeName] ==> bool ("_ ⊢ _ : _" [80, 80, 80] 80)

	where

	t_var : "Γ(x) = Some T ==> Γ ⊢ (Var x) : T"
	| t_abs : "\<lbrakk> Γ ⊢ "

translations
	Γ ⊢ t : T 

