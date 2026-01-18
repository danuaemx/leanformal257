import Erdos.ShellDefs
import Mathlib.Data.Nat.PrimeFin

namespace Erdos

namespace Erdos257

/--
`largestPrimeFactor n` is the largest prime factor of `n`.

For `n ≤ 1` we define it to be `1` (so the function is total). In shell arguments we typically
assume `1 ≤ n` and only use nontrivial behavior for `2 ≤ n`.

This matches the manuscript's `P(n)`.
-/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : 1 < n then
    n.primeFactors.max' ((Nat.nonempty_primeFactors).2 h)
  else
    1

/--
`ShellRespectsLevel shell P p` means: every index `n` placed in the `k`-th shell satisfies
`P n = p k`.

This is the bookkeeping form of manuscript shells of the shape
“`shell k = { n : ... | P(n) = p_k }`”.
-/
def ShellRespectsLevel (shell : Shell) (P : ℕ → ℕ) (p : ℕ → ℕ) : Prop :=
  ∀ k n, n ∈ shell k → P n = p k

/-- Convenience alias: shells described by the levels of the largest-prime-factor statistic. -/
def ShellRespectsLargestPrimeFactor (shell : Shell) (p : ℕ → ℕ) : Prop :=
  ShellRespectsLevel shell largestPrimeFactor p

/--
A shell hypothesis plus an explicit level condition.

This matches the phrasing “the sum `∑ log(n)/n` over the `P(n)=p_k` shell is `≪ 1`”.
-/
def DifferentialShellLogSmallOnLevels (A : Set ℕ) (shell : Shell) (P : ℕ → ℕ) (p : ℕ → ℕ) : Prop :=
  DifferentialShellLogSmall A shell ∧ ShellRespectsLevel shell P p

/-- Convenience alias: small log-moment shells, explicitly grouped by `largestPrimeFactor`. -/
def DifferentialShellLogSmallOnLargestPrimeFactor (A : Set ℕ) (shell : Shell) (p : ℕ → ℕ) : Prop :=
  DifferentialShellLogSmallOnLevels A shell largestPrimeFactor p

theorem DifferentialShellLogSmallOnLevels_iff (A : Set ℕ) (shell : Shell) (P : ℕ → ℕ) (p : ℕ → ℕ) :
    DifferentialShellLogSmallOnLevels A shell P p ↔
      (DifferentialShellLogSmall A shell ∧ ShellRespectsLevel shell P p) :=
  Iff.rfl

/-- The set of indices in `A` that belong to the `k`-th level `P n = p k`. -/
def levelSet (A : Set ℕ) (P : ℕ → ℕ) (p : ℕ → ℕ) (k : ℕ) : Set ℕ :=
  { n : ℕ | n ∈ A ∧ P n = p k }

/--
Build a concrete `Shell` from a level predicate, assuming each level-set is finite.

This is the clean Lean way to model manuscript shells like `ΔΨ_k ∩ A`, when one has already
restricted to a finite active set per level.
-/
noncomputable def shellOfFiniteLevels
    (A : Set ℕ) (P : ℕ → ℕ) (p : ℕ → ℕ)
    (hfin : ∀ k, (levelSet A P p k).Finite) : Shell :=
  fun k => (hfin k).toFinset

theorem shellOfFiniteLevels_mem_iff
    (A : Set ℕ) (P : ℕ → ℕ) (p : ℕ → ℕ)
    (hfin : ∀ k, (levelSet A P p k).Finite) (k n : ℕ) :
    n ∈ shellOfFiniteLevels A P p hfin k ↔ n ∈ A ∧ P n = p k := by
  classical
  -- `Finite.toFinset` has membership lemma `Set.mem_toFinset`.
  simp [shellOfFiniteLevels, levelSet]

theorem shellOfFiniteLevels_respectsLevel
    (A : Set ℕ) (P : ℕ → ℕ) (p : ℕ → ℕ)
    (hfin : ∀ k, (levelSet A P p k).Finite) :
    ShellRespectsLevel (shellOfFiniteLevels A P p hfin) P p := by
  intro k n hn
  have : n ∈ A ∧ P n = p k := (shellOfFiniteLevels_mem_iff A P p hfin k n).1 hn
  exact this.2

theorem shellOfFiniteLevels_subset
    (A : Set ℕ) (P : ℕ → ℕ) (p : ℕ → ℕ)
    (hfin : ∀ k, (levelSet A P p k).Finite) :
    ∀ k, (↑(shellOfFiniteLevels A P p hfin k) : Set ℕ) ⊆ A := by
  intro k n hn
  have : n ∈ A ∧ P n = p k := (shellOfFiniteLevels_mem_iff A P p hfin k n).1 hn
  exact this.1

/--
If there are infinitely many indices `k` with a nonempty level-set in `A`, then the shell built
from those levels has infinitely many nonempty shells.
-/
theorem infiniteShells_of_infinite_levels
    (A : Set ℕ) (P : ℕ → ℕ) (p : ℕ → ℕ)
    (hfin : ∀ k, (levelSet A P p k).Finite)
    (hinf : Set.Infinite { k : ℕ | ∃ n, n ∈ A ∧ P n = p k }) :
    InfiniteShells (shellOfFiniteLevels A P p hfin) := by
  -- Rewrite in terms of `Finset.Nonempty` using the membership lemma.
  classical
  -- Show the two index-sets are equal.
  have hset :
      { k : ℕ | (shellOfFiniteLevels A P p hfin k).Nonempty } =
        { k : ℕ | ∃ n, n ∈ A ∧ P n = p k } := by
    ext k
    constructor
    · intro hk
      rcases hk with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      exact (shellOfFiniteLevels_mem_iff A P p hfin k n).1 hn
    · rintro ⟨n, hnA, hnP⟩
      refine ⟨n, ?_⟩
      exact (shellOfFiniteLevels_mem_iff A P p hfin k n).2 ⟨hnA, hnP⟩
  -- Transfer infinitude across the definitional equality.
  simpa [InfiniteShells, hset] using hinf

/-!
### Witness selection on finite shells

In the manuscript (Phase 2), one selects inside each finite active shell an element maximizing
the $p$-adic valuation for the newly introduced prime. In this repo, the valuation surrogate is
`vp` from [Erdos/Basic.lean](Erdos/Basic.lean).

The lemmas below package the `exists_witness_vp` existence statement into a usable `choose`d
function.
-/

/-- Choose an element of a nonempty finite set maximizing `vp p ·`. -/
noncomputable def chooseWitnessVp (p : ℕ) (S : Finset ℕ) (hS : S.Nonempty) : ℕ :=
  Classical.choose (exists_witness_vp p S hS)

theorem chooseWitnessVp_mem (p : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    chooseWitnessVp p S hS ∈ S := by
  classical
  simpa [chooseWitnessVp] using (Classical.choose_spec (exists_witness_vp p S hS)).1

theorem chooseWitnessVp_isMax (p : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    ∀ m ∈ S, vp p m ≤ vp p (chooseWitnessVp p S hS) := by
  classical
  simpa [chooseWitnessVp] using (Classical.choose_spec (exists_witness_vp p S hS)).2

/-- Convenience: choose a witness in the `k`-th shell, maximizing `vp (p k) ·`. -/
noncomputable def shellWitness (shell : Shell) (p : ℕ → ℕ) (k : ℕ)
    (hk : (shell k).Nonempty) : ℕ :=
  chooseWitnessVp (p k) (shell k) hk

theorem shellWitness_mem (shell : Shell) (p : ℕ → ℕ) (k : ℕ)
    (hk : (shell k).Nonempty) : shellWitness shell p k hk ∈ shell k :=
  chooseWitnessVp_mem (p := p k) (S := shell k) hk

theorem shellWitness_isMax (shell : Shell) (p : ℕ → ℕ) (k : ℕ)
    (hk : (shell k).Nonempty) :
    ∀ m ∈ shell k, vp (p k) m ≤ vp (p k) (shellWitness shell p k hk) :=
  chooseWitnessVp_isMax (p := p k) (S := shell k) hk

end Erdos257

end Erdos
