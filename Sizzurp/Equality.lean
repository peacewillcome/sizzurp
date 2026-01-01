import Sizzurp.Naturals

namespace sizzurp

inductive Eq {α : Type} : α → α → Prop where
    | refl : ∀ n, Eq n n

notation:50 a " ~ " b => Eq a b

-- Symmetry: a ~ b → b ~ a
theorem eq_symm :  ∀ {α : Type} {a b : α}, (a ~ b) → b ~ a :=
    fun h => match h with | Eq.refl _ => Eq.refl _

-- Transitivity: a ~ b, b ~ c → a ~ c
theorem eq_trans : ∀ {α : Type} {a b c: α}, (a ~ b) → (b ~ c) → a ~ c :=
    fun h1 h2 => match h1, h2 with | Eq.refl _, Eq.refl _ => Eq.refl _

-- Successor congruence: ?
theorem s_c : ∀ {n m : Nat}, (n ~ m) → (n++ ~ m++) :=


end sizzurp
