import Erdos.Basic
import Erdos.RationalPeriodAlignment
import Erdos.ShellLevels
import Erdos.TokenBijection
import Erdos.HazardMaps
import Erdos.ShellStage
import Erdos.HazardCounting
import Erdos.HazardTokenCard
import Erdos.ShellDensity
import Erdos.ShellIrrationality
import Erdos.ShellToKernelBridge
import Erdos.ShellToRationalModelRecursion
import Erdos.ShellBoundaryStability
import Erdos.BlockModelNoCarry
import Erdos.ShellStageNoSubPeriod
import Erdos.FullClaim

namespace Erdos

namespace Erdos257

/--
Fully integrated *statement* of the shell-criterion theorem.

Let `A` be an infinite subset of naturals and `b ≥ 2`. Assume positivity on indices and that the
Erdős series is already in the fractional regime `erdosSeries b A < 1`.

If there exists a shell decomposition whose per-shell log-moment is uniformly `≪ 1`
(encoded as `DifferentialShellLogSmall A shell`), then the series is irrational.

This is the “all parts in one place” theorem statement you asked for; it is currently a `Prop`
because the construction turning the shell bound into a `KernelPackage` has not yet been fully
formalized in this repo.
-/
def erdos257_shellCriterion_under_one (b : ℕ) (A : Set ℕ) : Prop :=
  2 ≤ b → A.Infinite → (∀ n ∈ A, 1 ≤ n) →
    erdosSeries b A < 1 →
    (∃ shell : Shell, DifferentialShellLogSmall A shell) →
    Irrational (erdosSeries b A)

/--
Same shell criterion statement, but with the shell described explicitly as “levels of `P`”.

This is the version you requested: the analytic hypothesis is stated as
`∃ shell, DifferentialShellLogSmall A shell ∧ (∀ n ∈ shell k, P n = p k)`,
so one can read it as “for each `k`, the sum `∑ log(n)/n` over the `P(n)=p_k` shell is `≪ 1`”.
-/
def erdos257_shellCriterion_under_one_onLevels (b : ℕ) (A : Set ℕ)
    (P : ℕ → ℕ) (p : ℕ → ℕ) : Prop :=
  2 ≤ b → A.Infinite → (∀ n ∈ A, 1 ≤ n) →
    erdosSeries b A < 1 →
    (∃ shell : Shell, DifferentialShellLogSmallOnLevels A shell P p) →
    Irrational (erdosSeries b A)

/--
Specialization of `erdos257_shellCriterion_under_one_onLevels` to the manuscript choice
`P(n) =` largest prime factor of `n`.
-/
def erdos257_shellCriterion_under_one_onLargestPrimeFactor (b : ℕ) (A : Set ℕ) (p : ℕ → ℕ) : Prop :=
  erdos257_shellCriterion_under_one_onLevels b A largestPrimeFactor p

/--
Same as `erdos257_shellCriterion_under_one_onLargestPrimeFactor`, but additionally requiring
that the shell decomposition has infinitely many nonempty shells.

This matches the manuscript wording “infinitely many differential shells `P(n)=p_k`”.
-/
def erdos257_shellCriterion_under_one_onLargestPrimeFactor_infiniteShells
    (b : ℕ) (A : Set ℕ) (p : ℕ → ℕ) : Prop :=
  2 ≤ b → A.Infinite → (∀ n ∈ A, 1 ≤ n) →
    erdosSeries b A < 1 →
    (∃ shell : Shell,
      DifferentialShellLogSmallOnLargestPrimeFactor A shell p ∧ InfiniteShells shell) →
    Irrational (erdosSeries b A)

/--
Concrete (axiom-free) theorem form of the shell criterion, assuming you have built the
analytic→kernel bridge `ShellToKernel b A`.

This is the “under `∑ log n / n ≪ 1` per shell, the Erdős series is irrational” statement
specialized to the fractional regime `erdosSeries b A < 1`.
-/
theorem erdos257_shellCriterion_under_one_of_shellToKernel
    {b : ℕ} {A : Set ℕ} [ShellToKernel b A] :
    erdos257_shellCriterion_under_one b A := by
  intro hb hA hpos _hlt hshell
  -- The proof does not actually use the extra hypothesis `erdosSeries b A < 1`.
  exact (shellLogMomentSmall_implies_irrational_of_shellToKernel
   (b := b) (A := A)) hb hA hpos hshell

/--
Explicit-on-levels version of `erdos257_shellCriterion_under_one_of_shellToKernel`.

The extra “`P(n)=p_k`” bookkeeping is currently unused by the proof (we only need the
log-moment smallness); it is included to make the statement match the manuscript wording.
-/
theorem erdos257_shellCriterion_under_one_onLevels_of_shellToKernel
    {b : ℕ} {A : Set ℕ} [ShellToKernel b A]
    (P : ℕ → ℕ) (p : ℕ → ℕ) :
    erdos257_shellCriterion_under_one_onLevels b A P p := by
  intro hb hA hpos hlt hshell
  rcases hshell with ⟨shell, hshell⟩
  -- Drop the level condition and apply the already-packaged bridge theorem.
  exact erdos257_shellCriterion_under_one_of_shellToKernel
   (b := b) (A := A) hb hA hpos hlt ⟨shell, hshell.1⟩

/--
Explicit largest-prime-factor version of
`erdos257_shellCriterion_under_one_onLevels_of_shellToKernel`.
-/
theorem erdos257_shellCriterion_under_one_onLargestPrimeFactor_of_shellToKernel
    {b : ℕ} {A : Set ℕ} [ShellToKernel b A]
    (p : ℕ → ℕ) :
    erdos257_shellCriterion_under_one_onLargestPrimeFactor b A p := by
  -- unfold the specialization and reuse the general theorem.
  intro hb hA hpos hlt hshell
  simpa [erdos257_shellCriterion_under_one_onLargestPrimeFactor] using
    (erdos257_shellCriterion_under_one_onLevels_of_shellToKernel (b := b) (A := A)
      (P := largestPrimeFactor) (p := p) hb hA hpos hlt hshell)

/--
Largest-prime-factor shell criterion with the extra “infinitely many shells” hypothesis,
assuming the analytic→kernel bridge `[ShellToKernel b A]`.

The proof only uses the small log-moment condition; `InfiniteShells` is recorded to match
the intended manuscript assumptions.
-/
theorem erdos257_shellCriterion_under_one_onLargestPrimeFactor_infiniteShells_of_shellToKernel
    {b : ℕ} {A : Set ℕ} [ShellToKernel b A]
    (p : ℕ → ℕ) :
    erdos257_shellCriterion_under_one_onLargestPrimeFactor_infiniteShells b A p := by
  intro hb hA hpos hlt hshell
  rcases hshell with ⟨shell, hshellSmall, _hinf⟩
  -- Drop `InfiniteShells` and apply the already-packaged largest-prime-factor theorem.
  exact erdos257_shellCriterion_under_one_onLargestPrimeFactor_of_shellToKernel
    (b := b) (A := A) (p := p) hb hA hpos hlt ⟨shell, hshellSmall⟩

theorem erdos257_shellCriterion_under_one_iff
    (b : ℕ) (A : Set ℕ) :
    erdos257_shellCriterion_under_one b A ↔
      shellLogMomentSmall_implies_irrational_under_one b A :=
  Iff.rfl

end Erdos257

end Erdos
