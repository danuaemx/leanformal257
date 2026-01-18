import Erdos.Basic
import Erdos.TokenBijection
import Erdos.ShellIrrationality
import Erdos.FullClaim

namespace Erdos

namespace Erdos257

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

theorem erdos257_shellCriterion_under_one_iff
    (b : ℕ) (A : Set ℕ) :
    erdos257_shellCriterion_under_one b A ↔
      shellLogMomentSmall_implies_irrational_under_one b A :=
  Iff.rfl

end Erdos257

end Erdos
