import Erdos.Basic
import Mathlib.Data.Nat.PrimeFin
import Erdos.TokenBijection
import Erdos.HazardMaps
import Erdos.ShellStage
import Erdos.HazardCounting
import Erdos.HazardTokenCard
import Erdos.ShellDensity
import Erdos.ShellIrrationality
import Erdos.FullClaim

namespace Erdos

namespace Erdos257

/--
`largestPrimeFactor n` is the largest prime factor of `n`.

For `n ≤ 1` we define it to be `1` (so that the function is total).
In the shell arguments in this repo we always assume `1 ≤ n`, and typically `2 ≤ n`
on the nontrivial shells.

This is the intended meaning of the manuscript's `P(n)`.
-/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : 1 < n then
    n.primeFactors.max' ((Nat.nonempty_primeFactors).2 h)
  else
    1

/--
`ShellRespectsLevel shell P p` means: every index `n` placed in the `k`-th shell satisfies
`P n = p k`.

This is the formal way to express manuscript-style shells of the form
“`shell k = { n : ... | P(n) = p_k }`” (e.g. when `P` is a prime-factor statistic).
-/
def ShellRespectsLevel (shell : Shell) (P : ℕ → ℕ) (p : ℕ → ℕ) : Prop :=
  ∀ k n, n ∈ shell k → P n = p k

/-- Convenience alias: shells described by the levels of the largest-prime-factor statistic. -/
def ShellRespectsLargestPrimeFactor (shell : Shell) (p : ℕ → ℕ) : Prop :=
  ShellRespectsLevel shell largestPrimeFactor p

/--
`DifferentialShellLogSmallOnLevels A shell P p` is exactly the usual analytic hypothesis
`∑_{n ∈ shell k} log(n)/n ≪ 1` (uniformly with constant `< 1`), together with the explicit
level condition `P(n) = p_k` for `n ∈ shell k`.

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

/--
Fully integrated *statement* (no axioms) of the shell-criterion theorem.

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
  exact (shellLogMomentSmall_implies_irrational_of_shellToKernel (b := b) (A := A)) hb hA hpos hshell

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
  exact erdos257_shellCriterion_under_one_of_shellToKernel (b := b) (A := A) hb hA hpos hlt ⟨shell, hshell.1⟩

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

theorem erdos257_shellCriterion_under_one_iff
    (b : ℕ) (A : Set ℕ) :
    erdos257_shellCriterion_under_one b A ↔
      shellLogMomentSmall_implies_irrational_under_one b A :=
  Iff.rfl

end Erdos257

end Erdos
