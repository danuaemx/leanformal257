import Erdos.ShellToRationalModelRecursion

namespace Erdos

namespace Erdos257

/--
Package the manuscript's fractional-regime assumption `erdosSeries b A < 1` as a typeclass.

This is convenient because the TeX boundary-stability argument is only valid once the series is
known to have no integer carry/overflow.
-/
class ErdosUnderOne (b : ℕ) (A : Set ℕ) : Prop where
  under_one : erdosSeries b A < 1

/--
Interface for the manuscript's *boundary stability / aligned blocks* step.

This is the precise place where the TeX proof uses the hypothesis `erdosSeries b A < 1` to control
carries and show that (after some index) the extracted block sequence obeys the same one-step
remainder recursion as the rational model.

Once this is available, the file `Erdos/ShellToRationalModelRecursion.lean` upgrades it to the full
`ShellToRationalModel` bridge.
-/
class ShellBoundaryStability (b : ℕ) (A : Set ℕ) [ShellToStageFamily A] : Type where
  eventually_blocks_rec_under_one :
    ∀ shell (hshell : DifferentialShellLogBound A shell) (q : ℚ),
      erdosSeries b A < 1 →
      erdosSeries b A = q →
        ∃ N,
          (ShellToStageFamily.blocks (A := A) shell hshell) N = ratStateNat b q N ∧
          (∀ n ≥ N,
            (ShellToStageFamily.blocks (A := A) shell hshell) (n + 1)
              = (b * (ShellToStageFamily.blocks (A := A) shell hshell n)) % q.den)

/--
`ShellBoundaryStability` plus the fractional-regime hypothesis gives the exact recurrence interface
`ShellToRemainderRecursion` needed downstream.
-/
noncomputable instance instShellToRemainderRecursion_of_boundaryStability
    {b : ℕ} {A : Set ℕ}
    [ShellToStageFamily A] [ShellBoundaryStability b A] [ErdosUnderOne b A] :
    ShellToRemainderRecursion b A where
  eventually_blocks_rec shell hshell q hq := by
    simpa using
      (ShellBoundaryStability.eventually_blocks_rec_under_one (b := b) (A := A)
        shell hshell q (ErdosUnderOne.under_one (b := b) (A := A)) hq)

end Erdos257

end Erdos
