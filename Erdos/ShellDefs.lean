import Erdos.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos

namespace Erdos257

open scoped BigOperators

/--
A `Shell` is a decomposition device: `shell k` is the finite set of indices `m`
that lie in the `k`-th “differential shell”.

In the manuscript, the natural differential shells (e.g. by largest prime factor) are
infinite in general; in Lean we work with `Finset ℕ` shells because the token/bijection
kernel operates stage-by-stage on finite data.
-/
def Shell := ℕ → Finset ℕ

/-- The log-moment of a shell: `∑_{m ∈ shell k} log(m) / m` (as a real number). -/
noncomputable def shellLogMoment (shell : Shell) (k : ℕ) : ℝ :=
  (shell k).sum (fun m => Real.log (m : ℝ) / (m : ℝ))

/--
`InfiniteShells shell` means: there are infinitely many indices `k` such that the `k`-th shell is
nonempty.
-/
def InfiniteShells (shell : Shell) : Prop :=
  Set.Infinite { k : ℕ | (shell k).Nonempty }

/--
A minimal hypothesis package matching the manuscript phrase
“the sum `∑ log(m)/m` in each differential shell is ≪ 1”.

`C` is the implied constant in the `≪ 1`.

Notes:
- We require `1 ≤ m` on each shell so `Real.log (m:ℝ)` behaves as expected.
- We also record that shells are subsets of `A` (so they are genuinely sums over `A`).
- The constant `C` is abstract.
-/
structure DifferentialShellLogBound (A : Set ℕ) (shell : Shell) : Prop where
  shell_subset : ∀ k, (↑(shell k) : Set ℕ) ⊆ A
  shell_pos : ∀ k m, m ∈ shell k → 1 ≤ m
  exists_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, shellLogMoment shell k ≤ C

/--
Version of the shell hypothesis that matches the intended “`≪ 1`” smallness: the uniform bound
constant can be taken *strictly less than 1*.
-/
structure DifferentialShellLogSmall (A : Set ℕ) (shell : Shell) : Prop where
  shell_subset : ∀ k, (↑(shell k) : Set ℕ) ⊆ A
  shell_pos : ∀ k m, m ∈ shell k → 1 ≤ m
  exists_small : ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧ ∀ k, shellLogMoment shell k ≤ C

theorem DifferentialShellLogSmall.toBound {A : Set ℕ} {shell : Shell}
    (h : DifferentialShellLogSmall A shell) : DifferentialShellLogBound A shell := by
  refine ⟨h.shell_subset, h.shell_pos, ?_⟩
  rcases h.exists_small with ⟨C, hC0, _hC1, hbound⟩
  exact ⟨C, hC0, hbound⟩

end Erdos257

end Erdos
