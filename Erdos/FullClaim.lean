import Erdos.Basic
import Erdos.ShellIrrationality

namespace Erdos

namespace Erdos257

/--
The *full* Erdős-257 claim (as a proposition): for every base `b ≥ 2` and every infinite index set
`A ⊆ ℕ` with `A ⊆ {n | 1 ≤ n}`, the series `erdosSeries b A` is irrational.

This is the unconditional end-goal statement; it is not yet proved in this repo.
-/
def erdos257_claim (b : ℕ) (A : Set ℕ) : Prop :=
  2 ≤ b → A.Infinite → (∀ n ∈ A, 1 ≤ n) → Irrational (erdosSeries b A)

/-- A convenient “fully quantified” version of `FullClaim`. -/
def erdos257 : Prop :=
  ∀ (b : ℕ) (A : Set ℕ), erdos257_claim b A

/--
The current Lean proof establishes the full claim *assuming* a `DensityPackage`.

More precisely:

* The combinatorial kernel needs only a `KernelPackage b A`.
* `DensityPackage b A` is a convenience wrapper that also bundles `b ≥ 2`, `A.Infinite`, and
  positivity assumptions.
-/
theorem erdos257_claim_of_densityPackage {b : ℕ} {A : Set ℕ} (pkg : DensityPackage b A) :
    erdos257_claim b A := by
  intro _hb _hA _hpos
  -- Those hypotheses are bundled inside `pkg`; the kernel proof only needs the three fields below.
  have kp : Erdos.Erdos257.KernelPackage b A :=
    { blocks := pkg.blocks
      unbounded := pkg.unbounded
      eventually_eq_ratStateNat := pkg.eventually_eq_ratStateNat }
  simpa [erdos257_claim] using (erdos257_generalized (b := b) (A := A) kp)

/--
Main theorem statement (shell form, **unproved** in this repo):

If the per-shell log-moment `∑ log(m)/m` is uniformly bounded (`≪ 1`), then
`erdosSeries b A` is irrational.

This is recorded as a `Prop` so it introduces no new axioms.

Implementation status (as of this workspace):

* The fully formal kernel is `KernelPackage → Irrational`.
* There is now also a fully formal *intermediate* bridge in
  [Erdos/ShellIrrationality.lean](Erdos/ShellIrrationality.lean):
  `ShellToStageFamily` lets you derive an explicit, witnessed unbounded block sequence
  from per-stage block distinctness + token surplus.
* The remaining missing piece to get a full `KernelPackage` from shell bounds is the
  rational-model bridge `eventually_eq_ratStateNat`.
-/
def erdos257_claim_shellLogBound (b : ℕ) (A : Set ℕ) : Prop :=
  shellLogMomentBound_implies_irrational b A

end Erdos257

end Erdos
