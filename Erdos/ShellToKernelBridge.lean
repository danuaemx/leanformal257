import Erdos.Basic
import Erdos.ShellIrrationality

namespace Erdos

namespace Erdos257

/--
Additional missing bridge layer: turn rationality of the Erdős series into eventual agreement of the
constructed block sequence with the finite-state rational model `ratStateNat`.

This is the “boundary stability / periodic expansion” step from the manuscript. In the current repo
we separate it from the *surplus/exhaustion* construction (`ShellToStageFamily`).
-/
class ShellToRationalModel (b : ℕ) (A : Set ℕ) [ShellToStageFamily A] : Type where
  eventually_eq_ratStateNat :
    ∀ shell (hshell : DifferentialShellLogBound A shell) (q : ℚ),
      erdosSeries b A = q →
        ∃ N, ∀ n ≥ N, (ShellToStageFamily.blocks (A := A) shell hshell) n = ratStateNat b q n

/--
If you can build a stage family with surplus (`ShellToStageFamily`) and you can also prove the
rational-model agreement for its extracted blocks (`ShellToRationalModel`), then you get the full
kernel package needed by the unconditional combinatorial argument.

This is the cleanest “Shell → Kernel” composition point.
-/
noncomputable def kernelOfShellToStageFamily
    {b : ℕ} {A : Set ℕ} [ShellToStageFamily A] [ShellToRationalModel b A]
    (shell : Shell) (hshell : DifferentialShellLogBound A shell) :
    Erdos.Erdos257.KernelPackage b A := by
  classical
  let fam := ShellToStageFamily.mkFamily (A := A) shell hshell
  let hsur := ShellToStageFamily.hasSurplus (A := A) shell hshell
  refine
    { blocks := Erdos.StageFamily.blocks fam hsur
      unbounded := ?_
      eventually_eq_ratStateNat := ?_ }
  · -- Unbounded range comes from the generic `StageFamily` construction.
    simpa [ShellToStageFamily.blocks, fam, hsur] using
      (Erdos.StageFamily.unbounded_blocks fam hsur)
  · -- The rational-model bridge is supplied by `ShellToRationalModel`.
    intro q hq
    simpa [ShellToStageFamily.blocks, fam, hsur] using
      (ShellToRationalModel.eventually_eq_ratStateNat (b := b) (A := A) shell hshell q hq)

/--
Instance-level packaging: `ShellToStageFamily` + `ShellToRationalModel` ⇒ `ShellToKernel`.
-/
noncomputable instance instShellToKernel_of_stageFamily_and_rationalModel
    {b : ℕ} {A : Set ℕ} [ShellToStageFamily A] [ShellToRationalModel b A] :
    ShellToKernel b A where
  mkKernel shell hshell := kernelOfShellToStageFamily (b := b) (A := A) shell hshell

end Erdos257

end Erdos
