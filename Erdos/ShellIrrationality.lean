import Erdos.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos.TokenBijection
import Erdos.BlockWitness
import Erdos.TokenKernelBridge

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
Version of the shell hypothesis that matches the intended “`≪ 1`” smallness: the uniform bound
constant can be taken *strictly less than 1*.

This is often the quantitatively correct condition needed to force “more safe blocks than hazards”.
It is stronger than `DifferentialShellLogBound` but still purely analytic.
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

/--
Bridge interface: a way to turn an analytic shell bound into the `KernelPackage` required by
the fully formal combinatorial kernel.

This is exactly the missing “bijective token argument + boundary stability” layer.
Once an instance of this class is provided (for the intended shells), the main implication
`(∃ shell, DifferentialShellLogBound A shell) → Irrational (erdosSeries b A)` becomes a
one-line consequence of `erdos257_generalized`.
-/
class ShellToKernel (b : ℕ) (A : Set ℕ) : Type where
  mkKernel : ∀ shell : Shell, DifferentialShellLogBound A shell → Erdos.Erdos257.KernelPackage b A

/--
Intermediate bridge: produce a family of per-stage block/tokens data with enough surplus.

This isolates the part of the manuscript where one shows:
- block values are distinct on each stage (injectivity), and
- the number of hazard tokens is eventually dominated by the number of available blocks.

From this, we can build a *witnessed* strictly increasing block-value sequence, hence unbounded.
The remaining missing piece for a full `KernelPackage` is the rational-model bridge
`eventually_eq_ratStateNat`.
-/
class ShellToStageFamily (A : Set ℕ) : Type where
  mkFamily : ∀ shell : Shell, DifferentialShellLogBound A shell → Erdos.StageFamily
  hasSurplus :
    ∀ shell (hshell : DifferentialShellLogBound A shell),
      Erdos.StageFamily.HasSurplus (mkFamily shell hshell)

namespace ShellToStageFamily

/-- The witnessed block-value sequence extracted from a shell bound (conditional bridge). -/
noncomputable def blocks
    {A : Set ℕ} [ShellToStageFamily A]
    (shell : Shell) (hshell : DifferentialShellLogBound A shell) : ℕ → ℕ :=
  let fam := ShellToStageFamily.mkFamily (A := A) shell hshell
  let hsur := ShellToStageFamily.hasSurplus (A := A) shell hshell
  Erdos.StageFamily.blocks fam hsur

theorem unbounded_blocks
    {A : Set ℕ} [ShellToStageFamily A]
    (shell : Shell) (hshell : DifferentialShellLogBound A shell) :
    ∀ N (s : Finset ℕ), ∃ n ≥ N, blocks (A := A) shell hshell n ∉ s := by
  classical
  -- Unfold to the generic `StageFamily.unbounded_blocks` lemma.
  dsimp [blocks]
  simpa using
    (Erdos.StageFamily.unbounded_blocks
      (F := ShellToStageFamily.mkFamily (A := A) shell hshell)
      (h := ShellToStageFamily.hasSurplus (A := A) shell hshell))

end ShellToStageFamily

/--
The manuscript’s **token/bijection step**, isolated as a standalone interface.

This is the point where one turns an analytic shell bound into a concrete block sequence
`blocks : ℕ → ℕ` with the two properties needed by the formal combinatorial kernel:

1. **Exhaustion:** `blocks` has unbounded range.
2. **Rational model:** if `erdosSeries b A = q`, then `blocks` eventually agrees with
   the rational finite-state recursion `ratStateNat b q`.

In your narrative, this is exactly the “bijective token argument”: the construction that
forces new blocks to appear (so no eventual periodicity is possible).

**Token/bijection package ⇒ irrationality** (proved).

This is the fully formal part: once you have a `KernelPackage b A`, irrationality follows.
-/
theorem irrational_of_kernelPackage
    {b : ℕ} {A : Set ℕ} (_hb : 2 ≤ b) (_hA : A.Infinite) (_hpos : ∀ n ∈ A, 1 ≤ n)
  (kp : Erdos.Erdos257.KernelPackage b A) :
    Irrational (erdosSeries b A) := by
  -- These ambient hypotheses are part of the global claim; the kernel proof only needs `kp`.
  exact erdos257_generalized (b := b) (A := A) kp

/--
Main theorem **statement only** (no axioms):

If the “differential shell log-moment” bound holds (the hypothesis
`∑ log(m)/m ≪ 1` per shell), then the Erdős series is irrational.

This is the exact implication you asked to record *without* introducing an axiom.
Proving it requires formalizing the bijective/token construction turning the shell bound
into a `KernelPackage`.
-/
def shellLogMomentBound_implies_irrational (b : ℕ) (A : Set ℕ) : Prop :=
  2 ≤ b → A.Infinite → (∀ n ∈ A, 1 ≤ n) →
    (∃ shell : Shell, DifferentialShellLogBound A shell) →
    Irrational (erdosSeries b A)

/-- Same goal, but assuming the quantitatively small shell bound `C < 1`. -/
def shellLogMomentSmall_implies_irrational (b : ℕ) (A : Set ℕ) : Prop :=
  2 ≤ b → A.Infinite → (∀ n ∈ A, 1 ≤ n) →
    (∃ shell : Shell, DifferentialShellLogSmall A shell) →
    Irrational (erdosSeries b A)

/--
Main theorem statement in the form you requested (statement-only, no axioms):

Let `A` be infinite. Assume the Erdős series is already in the fractional regime
`erdosSeries b A < 1` (no integer carry/overflow). If, in addition, the per-shell log-moment
bound `∑ log(m)/m ≪ 1` holds (encoded as `DifferentialShellLogSmall`), then the series is
irrational.

This is the exact target statement for the analytic + token/bijection layer.
-/
def shellLogMomentSmall_implies_irrational_under_one (b : ℕ) (A : Set ℕ) : Prop :=
  2 ≤ b → A.Infinite → (∀ n ∈ A, 1 ≤ n) →
    erdosSeries b A < 1 →
    (∃ shell : Shell, DifferentialShellLogSmall A shell) →
    Irrational (erdosSeries b A)

/--
Implemented implication: assuming a bridge instance `ShellToKernel b A`, the shell-bound
statement holds.

This keeps the repo axiom-free while still giving you a *usable* theorem:
once you later construct an instance `ShellToKernel b A` from the manuscript’s token/bijection
and analytic estimates, the desired irrationality result follows immediately.
-/
theorem shellLogMomentBound_implies_irrational_of_shellToKernel
    {b : ℕ} {A : Set ℕ} [ShellToKernel b A] :
    shellLogMomentBound_implies_irrational b A := by
  intro hb hA hpos hShell
  rcases hShell with ⟨shell, hshell⟩
  have kp : Erdos.Erdos257.KernelPackage b A :=
    ShellToKernel.mkKernel (b := b) (A := A) shell hshell
  exact irrational_of_kernelPackage (b := b) (A := A) hb hA hpos kp

theorem shellLogMomentSmall_implies_irrational_of_shellToKernel
    {b : ℕ} {A : Set ℕ} [ShellToKernel b A] :
    shellLogMomentSmall_implies_irrational b A := by
  intro hb hA hpos hShell
  rcases hShell with ⟨shell, hshell⟩
  refine shellLogMomentBound_implies_irrational_of_shellToKernel (b := b) (A := A) hb hA hpos ?_
  exact ⟨shell, hshell.toBound⟩

end Erdos257

end Erdos
