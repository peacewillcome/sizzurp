namespace sizzurp

-- Reflexivity: a ~ a
inductive Eq : α → α → Prop where
    | refl : ∀ n, Eq n n

notation:50 a " ~ " b => Eq a b

-- Symmetry: a ~ b → b ~ a
theorem eq_symm :  ∀ {a b : α}, (a ~ b) → b ~ a :=
    fun h => match h with | Eq.refl _ => Eq.refl _

-- Transitivity: a ~ b, b ~ c → a ~ c
theorem eq_trans : ∀ {a b c: α}, (a ~ b) → (b ~ c) → a ~ c :=
    fun h1 h2 => match h1, h2 with | Eq.refl _, Eq.refl _ => Eq.refl _

-- Substitution: if a ~ b, then P(a) → P(b)
theorem eq_sub : ∀ {P : α → Prop}, (a ~ b) → (P a) → (P b) :=
    fun h1 h2 => match h1 with | Eq.refl _ => h2

-- Function application: if a ~ b, then f a ~ f b
theorem eq_app : ∀ {f : α → β}, (a ~ b) → ((f a) ~ (f b)) :=
    fun {f} h => match h with | Eq.refl _ => Eq.refl (f _)

-- Function extensionality: if ∀ a f(a) ~ g(a) → f ~ g
axiom eq_funext {f g : α → β} : (∀ a, f a ~ g a) → f ~ g

end sizzurp
