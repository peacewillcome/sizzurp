import Sizzurp.Equality

namespace sizzurp

inductive Nat where
    | zero : Nat
    | succ (n : Nat) : Nat
deriving Repr

notation "ℕ" => Nat

open Nat

-- Axiom 2.1: 0 is a natural number
instance instZero : Zero Nat := ⟨zero⟩

-- Axiom 2.2: if n is a natural number, then n++ is also a natural number
postfix:100 "++" => Nat.succ

-- Definition 2.3: numeral system
instance instOfNat {n : _root_.Nat} : OfNat Nat n where
    ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

-- Axiom 2.3: 0 is not the successor of any natural number
theorem succ_ne : ¬(n++ ~ 0) :=
    sorry

-- Successor congruence: ?
theorem succ_con : ∀ {n m : Nat}, (n ~ m) → (n++ ~ m++) :=
    eq_app

-- Proposition 2.1.6: 4 is not equal to 0
theorem four_ne_zero : 4 ≠ 0 :=
    fun h => nomatch h

-- Axiom 2.4: if n++ ~ m++, then n ~ m
theorem succ_eq_self_eq (h : n++ ~ m++) : n ~ m :=
    sorry

-- Axiom 2.5: if P(0) and if P(n) → P(n++), then ∀ n, P(n)
theorem induction {P : Nat → Prop} (b : P 0) (i : ∀ n, P n → P (n++)) : ∀ n, P n :=
    fun n =>
        match n with
        | 0 => b
        | n++ => i n (induction b i n)

-- Proposition 2.1.16: Recursion
abbrev recursion (f : Nat → Nat → Nat) (c : Nat) : Nat → Nat :=
    fun n =>
        match n with
        | 0 => c
        | n++ => f n (recursion f c n)

-- Proposition 2.1.16: index 0 ~ c
theorem recursion_zero (f : Nat → Nat → Nat) (c : Nat) : recursion f c 0 ~ c :=
    Eq.refl _

-- Proposition 2.1.16: a_n++ ~ f_n(a_n)
theorem recursion_succ (f : Nat → Nat → Nat) (c n : Nat) :
    recursion f c (n++) ~ f n (recursion f c n) := Eq.refl _

-- Proposition 2.1.16: definition is equal to code
theorem eq_recursion (f : Nat → Nat → Nat) (c : Nat) (a : Nat → Nat) :
    ((a 0 ~ c) ∧ ∀ n, a (n++) ~ f n (a n)) ↔ a ~ recursion f c :=
        ⟨
            (fun ⟨b, s⟩ =>
                eq_funext (
                    induction b (
                        fun n ih =>
                            eq_trans
                                (s n)
                                (eq_trans
                                    (eq_app ih)
                                    (recursion_succ f c n))
                        )
                    )
            ), (fun rhs =>
                ⟨(eq_congrFun rhs) 0, fun n =>
                    eq_trans
                        (eq_congrFun rhs (n++))
                        (eq_trans
                            (recursion_succ f c n)
                            (eq_symm (eq_app (eq_congrFun rhs n))))
                ⟩
            )
        ⟩

theorem uq_recursion (f : Nat → Nat → Nat) (c : Nat) :
    ∃ (a : Nat → Nat),
    ((a 0 ~ c) ∧ ∀ n, a (n++) ~ f n (a n)) ∧ ∀ b : Nat → Nat,
    ((b 0 ~ c) ∧ ∀ n, b (n++) ~ f n (b n)) → b ~ a :=
    ⟨
        recursion f c,
        ⟨
            ⟨recursion_zero f c, recursion_succ f c⟩,
            (fun a y => (eq_recursion f c a).mp y)
        ⟩
    ⟩

-- Addition
abbrev add (n m : Nat) : Nat :=
    recursion (fun _ sum ↦ sum++) m n

infix:65 " + " => add

#eval(add 6 0)
#eval(add 0 6 ~ add 6 0)

--?
theorem add_comm : ∀ {n m : Nat}, (n + m) ~ (m + n) :=
    sorry

-- Lemma 2.2.2: ∀ n, n + 0 ~ n
theorem add_zero : ∀ n, add n 0 ~ n :=
    fun n => induction (b := Eq.refl (add 0 0))

-- Addition congruence left: ?
theorem a_c_l : ∀ {a b c : Nat}, (b ~ c) → ((a+b) ~ (a+c)) :=
    sorry
