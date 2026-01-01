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

-- Axiom 2.3: 0 is not the sucessor of any natural number
theorem succ_ne : n++ ≠ 0 :=
    fun h => nomatch h

-- MISC 1
theorem fe3 : 4 = 3++ :=
    by rfl

-- Proposition 2.1.6: 4 is not equal to 0
theorem four_ne_zero : 4 ≠ 0 :=
    fun h => nomatch h

-- Axiom 2.4: if n++ = m++, then n = m
theorem succ_eq_self_eq {h : n++ = m++} : n = m :=
    succ.inj h
