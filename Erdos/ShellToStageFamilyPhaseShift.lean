import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Erdos.ShellDefs
import Erdos.ShellStage
import Erdos.ShellStageNoSubPeriod
import Erdos.ShellDensity
import Erdos.DensityProtection
import Erdos.TokenKernelBridge
import Erdos.BlockModelNoCarry

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

/--
Growing “next blocks” with no subperiods.

This connects the phase-shift stage construction with the “no ordinal simplification” property:
for every target length `N`, there exists a stage whose produced block word has length `> N` and
admits no subperiod.

In the manuscript language: we can pick shells far enough out so that the next block period is
both long and *not simplificable*.
-/
theorem exists_large_blockWord_noSubPeriod (spec : PhaseShiftStageSpec shell) (N : ℕ) :
    ∃ k : ℕ,
      let st := PhaseShiftStageSpec.stage (shell := shell) spec k
      let w := st.B.toList.map st.val
      N < w.length ∧ ¬ Erdos.Word.HasSubPeriod w := by
  classical
  -- Choose a stage with `μ` large compared to `N`.
  rcases spec.hμbig N with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  -- Unfold the stage and word definitions.
  let st := PhaseShiftStageSpec.stage (shell := shell) spec k
  let w := st.B.toList.map st.val
  have hnosub : ¬ Erdos.Word.HasSubPeriod w := by
    simpa [st, w] using (Erdos.ShellStage.not_hasSubPeriod_toList_map_val st)
  -- Compute the word length: here `st.B = blockIndices (μ k)`.
  have hwlen : w.length = spec.μ k := by
    -- `length (map _) = length`, `length_toList = card`, and `card_blockIndices = μ`.
    simp [w, st, PhaseShiftStageSpec.stage, Erdos.ShellStage.mkPhaseShift,
      Finset.length_toList, Erdos.card_blockIndices]
  have hNlt : N < w.length := by
    -- From `2*(N+1) < μ` we get `N < μ`.
    have hN1 : N + 1 ≤ 2 * (N + 1) := by
      simpa [two_mul] using Nat.le_add_left (N + 1) (N + 1)
    have hN1ltμ : N + 1 < spec.μ k := lt_of_le_of_lt hN1 hk
    have hNltμ : N < spec.μ k := lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_of_lt hN1ltμ)
    simpa [hwlen] using hNltμ
  exact ⟨hNlt, hnosub⟩

/--
Generalized-carry version (parametric): use the stage hazard set to define a finite `Bad` set of
indices for `concatWithCarryBlocks`, transfer the `shellLogMoment < 1/8` hypothesis into the
numeric form `4 * Bad.card < length`, and then conclude `¬ HasSubPeriod` using the existing
`BlockModel` lemmas.

What remains to be supplied for a concrete generalized-carry construction are exactly the two
local hypotheses from the manuscript:
- `hcarry0`: on good indices, no incoming carry enters the block;
- `hmod_inj`: on good indices, the no-carry residues `((baseBlock + p_i) % B)` are injective.
-/
theorem concatWithCarryBlocks_not_hasSubPeriod_of_hazards
    (spec : PhaseShiftStageSpec shell)
    (k : ℕ)
    (b L baseBlock : ℕ)
    (ps : List ℕ)
    (hpslen : ps.length = spec.μ k)
    (hL : L = spec.L k)
    (hdens8 : shellLogMoment shell k < (1 / 8 : ℝ))
    (hcarry0 :
      let st : Erdos.ShellStage :=
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
      let BadQ : Finset ℕ := (Erdos.ShellStage.hazardTokensOn st).image Erdos.ShellStage.Γ
      let Bad : Finset ℕ := BadQ.image (fun q => q - 1)
      ∀ (i : Fin ps.length), i.1 ∉ Bad →
        let carries := (Erdos.concatWithCarryTrace b L baseBlock ps).2.2
        carries[i.1 + 1]'
            (by
              have hc : carries.length = ps.length + 1 :=
                Erdos.concatWithCarryTrace_carries_length
                  (b := b) (L := L) (baseBlock := baseBlock) ps
              simpa [hc] using Nat.succ_lt_succ i.isLt) = 0)
    (hmod_inj :
      let st : Erdos.ShellStage :=
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
      let BadQ : Finset ℕ := (Erdos.ShellStage.hazardTokensOn st).image Erdos.ShellStage.Γ
      let Bad : Finset ℕ := BadQ.image (fun q => q - 1)
      ∀ (i j : Fin ps.length), i.1 ∉ Bad → j.1 ∉ Bad →
        ((baseBlock + ps.get i) % Erdos.blockBase b L) =
          ((baseBlock + ps.get j) % Erdos.blockBase b L) →
            i.1 = j.1) :
    ¬ Erdos.Word.HasSubPeriod (Erdos.concatWithCarryBlocks b L baseBlock ps) := by
  classical
  subst hL
  let st : Erdos.ShellStage :=
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
  let BadQ : Finset ℕ := (Erdos.ShellStage.hazardTokensOn st).image Erdos.ShellStage.Γ
  let Bad : Finset ℕ := BadQ.image (fun q => q - 1)

  have hμpos : 0 < st.μ := by
    -- direct from the spec, after unfolding the stage.
    simpa [st] using spec.hμpos k

  have hU4 : 4 * (Erdos.ShellStage.hazardTokensOn st).card < st.μ := by
    -- Apply the `1/8`-density lemma from `DensityProtection`.
    have hactive : st.active = shell k := by
      simp [st, Erdos.ShellStage.mkPhaseShift]
    have hcop : ∀ n ∈ st.active, Nat.Coprime st.L n := by
      intro n hn
      have : n ∈ shell k := by simpa [hactive] using hn
      simpa [st] using (spec.hcop k n this)
    have hm : ∀ n ∈ st.active, st.M n < n := by
      intro n hn
      have : n ∈ shell k := by simpa [hactive] using hn
      simpa [st] using (spec.hm k n this)
    have hne : ∀ n ∈ st.active, n ≠ 0 := by
      intro n hn
      have : n ∈ shell k := by simpa [hactive] using hn
      exact spec.hne k n this
    have hMlog : ∀ n ∈ shell k, (st.M n : ℝ) ≤ Real.log (n : ℝ) := by
      intro n hn
      simpa [st] using (spec.hMlog k n hn)

    simpa [hactive, st] using
      hazardTokensOn_card_four_mul_lt_mu_of_shellLogMoment_lt_eighth
        (shell := shell) (k := k) (st := st)
        (hμ := hμpos)
        (hactive := hactive)
        (hpos := by intro n hn; exact spec.hpos k n hn)
        (hleμ := by intro n hn; exact spec.hleμ k n hn)
        (hcop := hcop)
        (hm := hm)
        (hne := hne)
        (hMlog := hMlog)
        (hdens := hdens8)

  have hBad_le_U : Bad.card ≤ (Erdos.ShellStage.hazardTokensOn st).card := by
    -- two images: `card (image _) ≤ card` each time.
    have h1 : BadQ.card ≤ (Erdos.ShellStage.hazardTokensOn st).card := by
      simpa [BadQ] using (Finset.card_image_le)
    have h2 : Bad.card ≤ BadQ.card := by
      simpa [Bad] using (Finset.card_image_le)
    exact le_trans h2 h1

  have hden : 4 * Bad.card < (Erdos.concatWithCarryBlocks b (spec.L k) baseBlock ps).length := by
    have h4Bad_lt_mu : 4 * Bad.card < st.μ :=
      lt_of_le_of_lt (Nat.mul_le_mul_left 4 hBad_le_U) hU4
    have hl : (Erdos.concatWithCarryBlocks b (spec.L k) baseBlock ps).length = ps.length :=
      Erdos.concatWithCarryBlocks_length (b := b) (L := spec.L k) (baseBlock := baseBlock) ps
    -- rewrite `st.μ` to `spec.μ k` and then to `ps.length`.
    have : 4 * Bad.card < ps.length := by
      -- `st.μ = spec.μ k` by construction.
      simpa [st, hpslen] using h4Bad_lt_mu
    simpa [hl] using this

  have hcarry0' :
      ∀ (i : Fin ps.length), i.1 ∉ Bad →
        let carries := (Erdos.concatWithCarryTrace b (spec.L k) baseBlock ps).2.2
        carries[i.1 + 1]'
            (by
              have hc : carries.length = ps.length + 1 :=
                Erdos.concatWithCarryTrace_carries_length
                  (b := b) (L := spec.L k) (baseBlock := baseBlock) ps
              simpa [hc] using Nat.succ_lt_succ i.isLt) = 0 := by
    simpa [st, BadQ, Bad] using hcarry0

  have hmod_inj' :
      ∀ (i j : Fin ps.length), i.1 ∉ Bad → j.1 ∉ Bad →
        ((baseBlock + ps.get i) % Erdos.blockBase b (spec.L k)) =
          ((baseBlock + ps.get j) % Erdos.blockBase b (spec.L k)) →
            i.1 = j.1 := by
    simpa [st, BadQ, Bad] using hmod_inj

  have hinj :
      ∀ {i j : ℕ}
        (hi : i < (Erdos.concatWithCarryBlocks b (spec.L k) baseBlock ps).length)
        (hj : j < (Erdos.concatWithCarryBlocks b (spec.L k) baseBlock ps).length),
          i ∉ Bad → j ∉ Bad →
            (Erdos.concatWithCarryBlocks b (spec.L k) baseBlock ps).get ⟨i, hi⟩ =
              (Erdos.concatWithCarryBlocks b (spec.L k) baseBlock ps).get ⟨j, hj⟩ →
                i = j :=
    Erdos.BlockModel.concatWithCarryBlocks_hinj_of_goodNoCarry_of_mod_inj
      (b := b) (L := spec.L k) (baseBlock := baseBlock) (ps := ps) Bad
      hcarry0' hmod_inj'

  exact
    Erdos.BlockModel.concatWithCarryBlocks_not_hasSubPeriod_of_badDensity_lt_quarter
      (b := b) (L := spec.L k) (baseBlock := baseBlock) (ps := ps) (Bad := Bad)
      hden hinj

end PhaseShiftStageSpec

end Erdos257

end Erdos
