import Erdos.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos.TokenBijection

namespace Erdos

namespace Erdos257

open scoped BigOperators

/--
A `Shell` is an arbitrary decomposition device: `shell k` is the finite set of indices `m`
that lie in the `k`-th “differential shell”.

This file only *states* an analytic-to-irrationality theorem interface; it does not attempt
to build shells from primes/smooth numbers yet.
-/
def Shell := ℕ → Finset ℕ

/-- The log-moment of a shell: `∑_{m ∈ shell k} log(m) / m` (as a real number). -/
noncomputable def shellLogMoment (shell : Shell) (k : ℕ) : ℝ :=
  (shell k).sum (fun m => Real.log (m : ℝ) / (m : ℝ))

/--
A minimal hypothesis package matching the manuscript phrase
“the sum `∑ log(m)/m` in each differential shell is ≪ 1”.

`C` is the implied constant in the `≪ 1`.

Notes:
- We require `1 ≤ m` on each shell so `Real.log (m:ℝ)` behaves as expected.
- We also record that shells are subsets of `A` (so they are genuinely sums over `A`).
- The constant `C` is abstract; in applications you can pick `C = 1` or any other bound.
-/
structure DifferentialShellLogBound (A : Set ℕ) (shell : Shell) : Prop where
  shell_subset : ∀ k, (↑(shell k) : Set ℕ) ⊆ A
  shell_pos : ∀ k m, m ∈ shell k → 1 ≤ m
  exists_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, shellLogMoment shell k ≤ C

/--
The manuscript’s **token/bijection step**, isolated as a standalone interface.

This is the point where one turns an analytic shell bound into a concrete block sequence
`blocks : ℕ → ℕ` with the two properties needed by the formal combinatorial kernel:

1. **Exhaustion:** `blocks` has unbounded range.
2. **Rational model:** if `erdosSeries b A = q`, then `blocks` eventually agrees with
   the rational finite-state recursion `ratStateNat b q`.

In your narrative, this is exactly the “bijective token argument”: the construction that
forces new blocks to appear (so no eventual periodicity is possible).
-/
structure TokenBijectionPackage (b : ℕ) (A : Set ℕ) where
  blocks : ℕ → ℕ
  unbounded : ∀ N (s : Finset ℕ), ∃ n ≥ N, blocks n ∉ s
  eventually_eq_ratStateNat :
    ∀ q : ℚ, erdosSeries b A = q → ∃ N, ∀ n ≥ N, blocks n = ratStateNat b q n

/-- Convenience: the token package implies the `DensityPackage` interface used elsewhere. -/
noncomputable def densityPackage_of_tokenBijectionPackage
    {b : ℕ} {A : Set ℕ} (hb : 2 ≤ b) (hA : A.Infinite) (hpos : ∀ n ∈ A, 1 ≤ n)
    (tp : TokenBijectionPackage b A) :
    DensityPackage b A :=
  { hb := hb
    hA := hA
    hpos := hpos
    blocks := tp.blocks
    unbounded := tp.unbounded
    eventually_eq_ratStateNat := tp.eventually_eq_ratStateNat }

/--
**Token/bijection package ⇒ irrationality** (proved).

This is the fully formal part: once you have the block sequence `blocks` with the two kernel
properties (unboundedness and rational-model agreement), irrationality follows.
-/
theorem irrational_of_tokenBijectionPackage
    {b : ℕ} {A : Set ℕ} (hb : 2 ≤ b) (hA : A.Infinite) (hpos : ∀ n ∈ A, 1 ≤ n)
    (tp : TokenBijectionPackage b A) :
    Irrational (erdosSeries b A) := by
  exact erdos257_generalized (b := b) (A := A)
    (densityPackage_of_tokenBijectionPackage (b := b) (A := A) hb hA hpos tp)

/--
Main theorem **statement only** (no axioms):

If the “differential shell log-moment” bound holds (the hypothesis
`∑ log(m)/m ≪ 1` per shell), then the Erdős series is irrational.

This is the exact implication you asked to record *without* introducing an axiom.
Proving it requires formalizing the bijective/token construction turning the shell bound
into a `TokenBijectionPackage`.
-/
def shellLogMomentBound_implies_irrational (b : ℕ) (A : Set ℕ) : Prop :=
  2 ≤ b → A.Infinite → (∀ n ∈ A, 1 ≤ n) →
    (∃ shell : Shell, DifferentialShellLogBound A shell) →
    Irrational (erdosSeries b A)

end Erdos257

end Erdos
