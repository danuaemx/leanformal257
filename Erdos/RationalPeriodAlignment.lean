import Mathlib.Data.Nat.ModEq

import Erdos.Basic

namespace Erdos

namespace Erdos257

/-!
Small local iterator to avoid depending on `Function.iterate` lemmas.

`iter f L x` means apply `f` exactly `L` times to `x`.
-/

def iter {α : Type} (f : α → α) : ℕ → α → α
  | 0, x => x
  | Nat.succ n, x => iter f n (f x)

@[simp] theorem iter_zero {α : Type} (f : α → α) (x : α) : iter f 0 x = x := rfl

@[simp] theorem iter_succ {α : Type} (f : α → α) (n : ℕ) (x : α) :
    iter f (n + 1) x = iter f n (f x) := by
  cases n <;> rfl

theorem iter_apply {α : Type} (f : α → α) (n : ℕ) (x : α) :
    f (iter f n x) = iter f n (f x) := by
  induction n generalizing x with
  | zero => simp [iter]
  | succ n ih =>
      -- `iter f (n+1) x = iter f n (f x)`.
      simpa [iter, ih]

theorem ratState_succ (b : ℕ) (q : ℚ) (n : ℕ) :
    ratState b q (n + 1) = ratStep b q (ratState b q n) := by
  cases n <;> simp [ratState, ratStep, Nat.add_comm, Nat.add_left_comm]

theorem ratStateNat_succ (b : ℕ) (q : ℚ) (n : ℕ) :
    ratStateNat b q (n + 1) = (b * ratStateNat b q n) % q.den := by
  -- Unfold the state recursion and project to naturals.
  simp [ratStateNat, ratState_succ, ratStep, Nat.mul_mod]

theorem ratState_add (b : ℕ) (q : ℚ) (n L : ℕ) :
    ratState b q (n + L) = iter (ratStep b q) L (ratState b q n) := by
  induction L with
  | zero =>
      simp [iter]
  | succ L ih =>
      -- `n + (L+1) = (n+L) + 1` and unfold the recursion.
      have : ratState b q (n + (L + 1)) = ratStep b q (ratState b q (n + L)) := by
        simpa [Nat.add_assoc] using ratState_succ (b := b) (q := q) (n := n + L)
      -- Rewrite both sides using the induction hypothesis.
      -- The remaining goal is exactly `ratStep (iter …) = iter … (ratStep …)`.
      simpa [this, ih, Nat.add_assoc] using
        (iter_apply (f := ratStep b q) (n := L) (x := ratState b q n))

theorem ratStep_iterate_val (b : ℕ) (q : ℚ) :
    ∀ L (r : Fin q.den),
      (iter (ratStep b q) L r).1 = (b ^ L * r.1) % q.den := by
  intro L
  induction L with
  | zero =>
      intro r
    -- `iterate 0` is identity and `b^0 = 1`.
      have hr : (r.1) % q.den = r.1 := Nat.mod_eq_of_lt r.2
      simp [iter, ratStep, hr]
  | succ L ih =>
      intro r
      -- One more `ratStep` multiplies by `b` (mod `q.den`).
      have hprev : (iter (ratStep b q) L (ratStep b q r)).1 = (b ^ L * (ratStep b q r).1) % q.den :=
        ih (ratStep b q r)
      -- Expand `ratStep` and reduce the modular arithmetic to a single `mul_mod` simplification.
      have hmul :
          (b ^ L * ((b * r.1) % q.den)) % q.den = (b ^ L * (b * r.1)) % q.den := by
        -- Rewrite both sides with `Nat.mul_mod` and cancel `mod_mod`.
        simp [Nat.mul_mod, Nat.mod_mod, Nat.mul_assoc]
      -- Now assemble.
      calc
        (iter (ratStep b q) (L + 1) r).1
            = (iter (ratStep b q) L (ratStep b q r)).1 := by
                simp [iter, Nat.add_assoc]
        _ = (b ^ L * (ratStep b q r).1) % q.den := hprev
        _ = (b ^ L * ((b * r.1) % q.den)) % q.den := by
              simp [ratStep]
        _ = (b ^ L * (b * r.1)) % q.den := hmul
        _ = (b ^ (L + 1) * r.1) % q.den := by
              simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem ratStep_iterate_eq_self_of_pow_modEq_one
    (b : ℕ) (q : ℚ) (L : ℕ)
    (hpow : Nat.ModEq q.den (b ^ L) 1) (r : Fin q.den) :
  iter (ratStep b q) L r = r := by
  apply Fin.ext
  -- Reduce to a statement about remainders modulo `q.den`.
  have hval := ratStep_iterate_val (b := b) (q := q) (L := L) r
  -- `Nat.ModEq` is definitionally about `%`.
  have hpow' : (b ^ L) % q.den = (1 : ℕ) % q.den := by
    simpa [Nat.ModEq] using hpow
  -- Use `Nat.mul_mod` to push the congruence through multiplication.
  have : (b ^ L * r.1) % q.den = r.1 := by
    have hr : r.1 % q.den = r.1 := Nat.mod_eq_of_lt r.2
    calc
      (b ^ L * r.1) % q.den
          = ((b ^ L) % q.den * (r.1 % q.den)) % q.den := by
              simpa [Nat.mul_mod]
      _ = ((1 : ℕ) % q.den * (r.1 % q.den)) % q.den := by
              simp [hpow']
      _ = r.1 % q.den := by simp
      _ = r.1 := hr
  simpa [hval] using this

/--
If `b^L ≡ 1 (mod q.den)`, then the rational-state recursion is **periodic** with period `L`.

This is the formal version of the manuscript step “the sub-period divides the full period”,
expressed purely at the level of the remainder automaton.
-/
theorem ratStateNat_periodic_of_pow_modEq_one
    (b : ℕ) (q : ℚ) (L : ℕ)
    (hL : 0 < L)
    (hpow : Nat.ModEq q.den (b ^ L) 1) :
    EventuallyPeriodic (ratStateNat b q) := by
  refine ⟨L, hL, 0, ?_⟩
  intro n _
  have hstate : ratState b q (n + L) = ratState b q n := by
    calc
      ratState b q (n + L)
          = iter (ratStep b q) L (ratState b q n) :=
            ratState_add (b := b) (q := q) (n := n) (L := L)
      _ = ratState b q n := by
            simpa using
              (ratStep_iterate_eq_self_of_pow_modEq_one (b := b) (q := q) (L := L) hpow (ratState b q n))
  -- Project to naturals.
  simpa [ratStateNat, hstate]

end Erdos257

end Erdos
