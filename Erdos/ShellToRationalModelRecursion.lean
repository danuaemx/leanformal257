import Erdos.ShellToKernelBridge
import Erdos.RationalPeriodAlignment

namespace Erdos

namespace Erdos257

/--
A small interface isolating the exact *boundary stability ⇒ remainder recursion* step
from the manuscript.

If you can show that the extracted shell blocks eventually satisfy the same one-step
mod-`q.den` recurrence as `ratStateNat`, then you automatically get the full
`ShellToRationalModel` bridge.
-/
class ShellToRemainderRecursion (b : ℕ) (A : Set ℕ) [ShellToStageFamily A] : Type where
  eventually_blocks_rec :
    ∀ shell (hshell : DifferentialShellLogBound A shell) (q : ℚ),
      erdosSeries b A = q →
        ∃ N,
          (ShellToStageFamily.blocks (A := A) shell hshell) N = ratStateNat b q N ∧
          (∀ n ≥ N,
            (ShellToStageFamily.blocks (A := A) shell hshell) (n + 1)
              = (b * (ShellToStageFamily.blocks (A := A) shell hshell n)) % q.den)

private theorem eventually_eq_ratStateNat_of_eventually_rec
    {b : ℕ} {f : ℕ → ℕ} {q : ℚ} (N : ℕ)
    (h0 : f N = ratStateNat b q N)
    (hstep : ∀ n ≥ N, f (n + 1) = (b * f n) % q.den) :
    ∀ n ≥ N, f n = ratStateNat b q n := by
  intro n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
  induction m with
  | zero =>
      simpa using h0
  | succ m ih =>
      have hNm : N ≤ N + m := Nat.le_add_right N m
      have hf : f (N + m + 1) = (b * f (N + m)) % q.den := by
        simpa [Nat.add_assoc] using hstep (N + m) hNm
      have hrat : ratStateNat b q (N + m + 1) = (b * ratStateNat b q (N + m)) % q.den := by
        simpa [Nat.add_assoc] using (ratStateNat_succ (b := b) (q := q) (n := N + m))
      calc
        f (N + m + 1)
            = (b * f (N + m)) % q.den := hf
        _ = (b * ratStateNat b q (N + m)) % q.den := by simp [ih]
        _ = ratStateNat b q (N + m + 1) := by simpa [hrat]

/--
`ShellToRemainderRecursion` is exactly the missing ingredient needed to build
`ShellToRationalModel`.
-/
noncomputable instance instShellToRationalModel_of_remainderRecursion
    {b : ℕ} {A : Set ℕ} [ShellToStageFamily A] [ShellToRemainderRecursion b A] :
    ShellToRationalModel b A where
  eventually_eq_ratStateNat shell hshell q hq := by
    classical
    rcases ShellToRemainderRecursion.eventually_blocks_rec (b := b) (A := A) shell hshell q hq with
      ⟨N, h0, hstep⟩
    refine ⟨N, ?_⟩
    intro n hn
    exact eventually_eq_ratStateNat_of_eventually_rec (b := b)
      (f := ShellToStageFamily.blocks (A := A) shell hshell)
      (q := q) N h0 hstep n hn

end Erdos257

end Erdos
