import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Erdos.ShellDefs
import Erdos.ShellStage
import Erdos.ShellDensity
import Erdos.DensityProtection
import Erdos.TokenKernelBridge

namespace Erdos

namespace Erdos257

open scoped BigOperators

/--
A *parameter package* for constructing a `StageFamily` using the phase-shift stage
`q ↦ (q·L) mod μ` on each shell.

This file intentionally keeps the “analytic choices” explicit:
- how to pick `μ_k`, `L_k`, the witness term, and the carry-displacement bound `M_k(n)`;
- how to prove the side conditions (coprimality, `M<n`, `M≤log`, `n≤μ`);
- how to guarantee `μ` grows so the `StageFamily.HasSurplus` quantifier can be met.

Once you can instantiate this structure for your intended shells (e.g. by largest prime factor),
this module gives you the fully formal combinatorial conclusion:
`StageFamily.HasSurplus`.
-/
structure PhaseShiftStageSpec (shell : Shell) where
  μ : ℕ → ℕ
  L : ℕ → ℕ
  Mfun : ℕ → ℕ → ℕ
  witness : ℕ → ℕ

  hμ0 : ∀ k, μ k ≠ 0
  hμpos : ∀ k, 0 < μ k
  hcopμ : ∀ k, Nat.Coprime (L k) (μ k)

  hwitness : ∀ k, witness k ∈ shell k

  hpos : ∀ k n, n ∈ shell k → 1 ≤ n
  hleμ : ∀ k n, n ∈ shell k → n ≤ μ k

  hcop : ∀ k n, n ∈ shell k → Nat.Coprime (L k) n
  hm : ∀ k n, n ∈ shell k → Mfun k n < n
  hne : ∀ k n, n ∈ shell k → n ≠ 0
  hMlog : ∀ k n, n ∈ shell k → (Mfun k n : ℝ) ≤ Real.log (n : ℝ)

  /-- Per-shell density smallness (the manuscript’s “≪ 1”, specialized to `< 1/4`). -/
  hdens : ∀ k, shellLogMoment shell k < (1 / 4 : ℝ)

  /-- Growth condition: for each forbidden prefix length `M`, some stage has `μ > 2*(M+1)`. -/
  hμbig : ∀ M : ℕ, ∃ k, 2 * (M + 1) < μ k

namespace PhaseShiftStageSpec

variable {shell : Shell}

/-- The `k`-th phase-shift `ShellStage` associated to a spec. -/
noncomputable def stage (spec : PhaseShiftStageSpec shell) (k : ℕ) : Erdos.ShellStage := by
  classical
  exact
    Erdos.ShellStage.mkPhaseShift
      (μ := spec.μ k)
      (L := spec.L k)
      (hμ := spec.hμ0 k)
      (hcop := spec.hcopμ k)
      (active := shell k)
      (M := spec.Mfun k)
      (B := blockIndices (spec.μ k))
      (hB := by intro q hq; exact hq)
      (witness := spec.witness k)
      (hwitness := spec.hwitness k)

/-- The `StageFamily` obtained by applying `toBlockStage` stagewise. -/
noncomputable def stageFamily (spec : PhaseShiftStageSpec shell) : Erdos.StageFamily (ℕ × ℕ) where
  stage k := (stage spec k).toBlockStage

/--
Surplus for the phase-shift stage family, assuming `PhaseShiftStageSpec`.

This is the formal “density ⇒ surplus” step extracted from `DensityProtection`.
-/
theorem hasSurplus_stageFamily (spec : PhaseShiftStageSpec shell) :
  Erdos.StageFamily.HasSurplus (stageFamily spec) := by
  intro M
  rcases spec.hμbig M with ⟨k, hμbig⟩
  refine ⟨k, ?_⟩
  -- Apply the kernel-facing surplus lemma to the stage at `k`.
  have hμ0 : spec.μ k ≠ 0 := spec.hμ0 k
  have hμpos : 0 < spec.μ k := spec.hμpos k
  have hcopμ : Nat.Coprime (spec.L k) (spec.μ k) := spec.hcopμ k
  have hwitness : spec.witness k ∈ shell k := spec.hwitness k

  -- Unfold the family stage; it is `toBlockStage` of the constructed shell stage.
  -- We keep the stage as a `let` to match the statement of `phaseShift_surplus_of_density_quarter`.
  let st : Erdos.ShellStage :=
    Erdos.ShellStage.mkPhaseShift (μ := spec.μ k) (L := spec.L k)
      (hμ := hμ0) (hcop := hcopμ) (active := shell k) (M := spec.Mfun k)
      (B := blockIndices (spec.μ k)) (hB := by intro q hq; exact hq)
      (witness := spec.witness k) (hwitness := hwitness)

  have hsur :
      st.toBlockStage.U.card + (M + 1) < st.toBlockStage.B.card := by
    -- all hypotheses are provided by `spec`.
    simpa [st] using
      (phaseShift_surplus_of_density_quarter
        (shell := shell) (k := k)
        (μ := spec.μ k) (L := spec.L k)
        (hμ0 := hμ0) (hcopμ := hcopμ)
        (active := shell k) (Mfun := spec.Mfun k)
        (witness := spec.witness k) (hwitness := hwitness)
        (hμ := hμpos)
        (hactive := rfl)
        (hpos := by intro n hn; exact spec.hpos k n hn)
        (hleμ := by intro n hn; exact spec.hleμ k n hn)
        (hcop := by intro n hn; exact spec.hcop k n hn)
        (hm := by intro n hn; exact spec.hm k n hn)
        (hne := by intro n hn; exact spec.hne k n hn)
        (hMlog := by intro n hn; exact spec.hMlog k n hn)
        (hdens := spec.hdens k)
        (M := M) (hμbig := hμbig))

  -- Now rewrite back to the `StageFamily` stage.
  -- `stageFamily spec).stage k` is definitional equal to `st.toBlockStage`.
  simpa [stageFamily, PhaseShiftStageSpec.stage, st] using hsur

end PhaseShiftStageSpec

end Erdos257

end Erdos
