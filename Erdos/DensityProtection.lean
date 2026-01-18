import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Card

import Erdos.ShellDensity
import Erdos.PhaseShift

namespace Erdos

open scoped BigOperators

/-- `{1,…,μ}` is definitionally the Nat interval `Icc 1 μ`. -/
theorem blockIndices_eq_Icc (μ : ℕ) : blockIndices μ = Finset.Icc 1 μ := by
  ext q
  constructor <;> intro h
  · have h' : q ∈ (Finset.range (μ + 1)).filter (fun q => 1 ≤ q) := by
      simpa [blockIndices] using h
    have hqrange : q ∈ Finset.range (μ + 1) := (Finset.mem_filter.1 h').1
    have hqge : 1 ≤ q := (Finset.mem_filter.1 h').2
    have hqle : q ≤ μ := by
      exact Nat.lt_succ_iff.mp (Finset.mem_range.1 hqrange)
    exact Finset.mem_Icc.2 ⟨hqge, hqle⟩
  · have hq : 1 ≤ q ∧ q ≤ μ := (Finset.mem_Icc.1 h)
    have hqrange : q ∈ Finset.range (μ + 1) := by
      exact Finset.mem_range.2 (Nat.lt_succ_iff.mpr hq.2)
    exact Finset.mem_filter.2 ⟨hqrange, hq.1⟩

/-- `blockIndices μ` has cardinality `μ`. -/
theorem card_blockIndices (μ : ℕ) : (blockIndices μ).card = μ := by
  classical
  -- Reduce to `Icc`.
  simp [blockIndices_eq_Icc]

namespace ShellStage

/-- If `st.B = blockIndices st.μ`, then `hazardTokensOn st` is the full hazard universe. -/
theorem hazardTokensOn_eq_hazardTokens_of_B_eq
    (st : Erdos.ShellStage) (hBfull : st.B = blockIndices st.μ) :
    hazardTokensOn st = hazardTokens st.μ st.L st.M st.active := by
  classical
  simp [ShellStage.hazardTokensOn, hazardTokens, hBfull]

end ShellStage

namespace Erdos257

/--
Under the manuscript-style density bound `shellLogMoment shell k < 1/2` (together with the local
hypotheses used in [Erdos/ShellDensity.lean](Erdos/ShellDensity.lean)), the hazard universe
occupies strictly fewer than `μ` blocks.

This is the “carry protected” inequality: there is at least one safe block index.
-/
theorem hazardTokensOn_card_lt_mu_of_shellLogMoment_lt_half
    (shell : Shell) (k : ℕ) (st : Erdos.ShellStage)
    (hμ : 0 < st.μ)
    (hactive : st.active = shell k)
    (hpos : ∀ n ∈ shell k, 1 ≤ n)
    (hleμ : ∀ n ∈ shell k, n ≤ st.μ)
    (hcop : ∀ n ∈ st.active, Nat.Coprime st.L n)
    (hm : ∀ n ∈ st.active, st.M n < n)
    (hne : ∀ n ∈ st.active, n ≠ 0)
    (hMlog : ∀ n ∈ shell k, (st.M n : ℝ) ≤ Real.log (n : ℝ))
    (hdens : shellLogMoment shell k < (1 / 2 : ℝ)) :
    (Erdos.ShellStage.hazardTokensOn st).card < st.μ := by
  classical
  have hμR : (0 : ℝ) < (st.μ : ℝ) := by exact_mod_cast hμ
  have hdens_le : ((Erdos.ShellStage.hazardTokensOn st).card : ℝ) / (st.μ : ℝ)
      ≤ 2 * shellLogMoment shell k :=
    hazardTokensOn_density_le_two_mul_shellLogMoment
      (shell := shell) (k := k) (st := st)
      hμ hactive hpos hleμ hcop hm hne hMlog
  have hfrac : ((Erdos.ShellStage.hazardTokensOn st).card : ℝ) / (st.μ : ℝ) < 1 := by
    have : 2 * shellLogMoment shell k < (1 : ℝ) := by
      nlinarith
    exact lt_of_le_of_lt hdens_le this
  have hcardR : ((Erdos.ShellStage.hazardTokensOn st).card : ℝ) < (st.μ : ℝ) := by
    -- `a/μ < 1` with `0 < μ` implies `a < μ`.
    have := (div_lt_iff₀ hμR).1 hfrac
    simpa using this
  exact_mod_cast hcardR

/--
If blocks are made distinct by the phase shift `val q = (q·L) mod μ` (so `hinj` holds), and the
shell density is small enough that `< μ/2`, then there exists a safe block index not corrupted
by carries.

This packages the two key facts you asked for:
- **distinct blocks**: via `phaseShiftNat` injectivity, and
- **carry protected**: via the density bound implying `|U| < |B|`.
-/
theorem exists_safeBlock_phaseShift_of_density
    (shell : Shell) (k : ℕ)
    (μ L : ℕ) (hμ0 : μ ≠ 0) (hcopμ : Nat.Coprime L μ)
    (active : Finset ℕ) (M : ℕ → ℕ)
    (witness : ℕ) (hwitness : witness ∈ active)
    (hμ : 0 < μ)
    (hactive : active = shell k)
    (hpos : ∀ n ∈ shell k, 1 ≤ n)
    (hleμ : ∀ n ∈ shell k, n ≤ μ)
    (hcop : ∀ n ∈ active, Nat.Coprime L n)
    (hm : ∀ n ∈ active, M n < n)
    (hne : ∀ n ∈ active, n ≠ 0)
    (hMlog : ∀ n ∈ shell k, (M n : ℝ) ≤ Real.log (n : ℝ))
    (hdens : shellLogMoment shell k < (1 / 2 : ℝ)) :
    ∃ b ∈ blockIndices μ,
      b ∉ (Erdos.ShellStage.hazardTokensOn
            (Erdos.ShellStage.mkPhaseShift μ L hμ0 hcopμ active M (blockIndices μ) (by
              intro q hq
              exact hq) witness hwitness)).image Erdos.ShellStage.Γ := by
  classical
  haveI : NeZero μ := ⟨hμ0⟩
  -- Use the phase-shift stage with full block indices.
  let st : Erdos.ShellStage :=
    Erdos.ShellStage.mkPhaseShift μ L hμ0 hcopμ active M (blockIndices μ)
      (by intro q hq; exact hq) witness hwitness
  have hcardU : (Erdos.ShellStage.hazardTokensOn st).card < μ := by
    -- Apply the general density-to-`< μ` lemma.
    simpa [st] using
      (hazardTokensOn_card_lt_mu_of_shellLogMoment_lt_half
        (shell := shell) (k := k) (st := st)
        (hμ := hμ) (hactive := by simpa [st] using hactive)
        (hpos := hpos) (hleμ := hleμ)
        (hcop := by simpa [st] using hcop)
        (hm := by simpa [st] using hm)
        (hne := by simpa [st] using hne)
        (hMlog := by simpa [st, hactive] using hMlog)
        (hdens := hdens))
  -- Convert to the `BlockStage` inequality and pick a safe block.
  have hBcard' : st.B.card = μ := by
    simp [st, Erdos.ShellStage.mkPhaseShift, card_blockIndices]
  have hBcard : st.toBlockStage.B.card = μ := by
    simpa [ShellStage.toBlockStage, hBcard']
  have hU_lt_B : st.toBlockStage.U.card < st.toBlockStage.B.card := by
    -- Here `st.toBlockStage.U = hazardTokensOn st` and `st.toBlockStage.B = blockIndices μ`.
    simpa [ShellStage.toBlockStage, hBcard'] using hcardU
  have hcard : st.toBlockStage.U.card + (0 : ℕ) < st.toBlockStage.B.card := by
    simpa using hU_lt_B
  rcases BlockStage.exists_safeBlock_avoiding (st := st.toBlockStage) (S := (∅ : Finset ℕ)) hcard with
    ⟨b, hbB, hbnotHit, _hbval⟩
  refine ⟨b, hbB, ?_⟩
  simpa [ShellStage.Γ] using hbnotHit

/--
Kernel-facing “surplus” inequality for the phase-shift stage.

This is the exact shape required by `StageFamily.HasSurplus`:
`U.card + (M+1) < B.card`.

Compared to `hazardTokensOn_card_lt_mu_of_shellLogMoment_lt_half`, this needs a stricter
density bound (`< 1/4`) plus a lower bound on `μ` relative to `M`.

Once you have a way to pick stages with arbitrarily large `μ` (as in the manuscript),
this lemma is the missing combinatorial input to build a `StageFamily.HasSurplus` instance.
-/
theorem phaseShift_surplus_of_density_quarter
    (shell : Shell) (k : ℕ)
    (μ L : ℕ) (hμ0 : μ ≠ 0) (hcopμ : Nat.Coprime L μ)
    (active : Finset ℕ) (Mfun : ℕ → ℕ)
    (witness : ℕ) (hwitness : witness ∈ active)
    (hμ : 0 < μ)
    (hactive : active = shell k)
    (hpos : ∀ n ∈ shell k, 1 ≤ n)
    (hleμ : ∀ n ∈ shell k, n ≤ μ)
    (hcop : ∀ n ∈ active, Nat.Coprime L n)
    (hm : ∀ n ∈ active, Mfun n < n)
    (hne : ∀ n ∈ active, n ≠ 0)
    (hMlog : ∀ n ∈ shell k, (Mfun n : ℝ) ≤ Real.log (n : ℝ))
    (hdens : shellLogMoment shell k < (1 / 4 : ℝ))
    (M : ℕ) (hμbig : 2 * (M + 1) < μ) :
    let st : Erdos.ShellStage :=
      Erdos.ShellStage.mkPhaseShift μ L hμ0 hcopμ active Mfun (blockIndices μ)
        (by intro q hq; exact hq) witness hwitness
    st.toBlockStage.U.card + (M + 1) < st.toBlockStage.B.card := by
  classical
  haveI : NeZero μ := ⟨hμ0⟩
  intro st
  have hμR : (0 : ℝ) < (μ : ℝ) := by exact_mod_cast hμ
  -- Density bound from `ShellDensity`.
  have hdens_le : ((Erdos.ShellStage.hazardTokensOn st).card : ℝ) / (μ : ℝ)
      ≤ 2 * shellLogMoment shell k :=
    hazardTokensOn_density_le_two_mul_shellLogMoment
      (shell := shell) (k := k) (st := st)
      (hμ := hμ) (hactive := by simpa [st] using hactive)
      (hpos := hpos) (hleμ := by simpa [st] using hleμ)
      (hcop := by simpa [st] using hcop)
      (hm := by simpa [st] using hm)
      (hne := by simpa [st] using hne)
      (hMlog := by simpa [st, hactive] using hMlog)
  have hfrac : ((Erdos.ShellStage.hazardTokensOn st).card : ℝ) / (μ : ℝ) < (1 / 2 : ℝ) := by
    have : (2 * shellLogMoment shell k : ℝ) < 1 / 2 := by
      nlinarith
    exact lt_of_le_of_lt hdens_le this
  have hU_lt_half : ((Erdos.ShellStage.hazardTokensOn st).card : ℝ) < (μ : ℝ) / 2 := by
    -- from `U/μ < 1/2` and `μ > 0`
    have := (div_lt_iff₀ hμR).1 hfrac
    -- rewrite `μ * (1/2)` as `μ/2`
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using this
  have hM_lt_half : (M + 1 : ℝ) < (μ : ℝ) / 2 := by
    have hμbigR : (2 * (M + 1) : ℝ) < (μ : ℝ) := by exact_mod_cast hμbig
    -- divide by `2 > 0`
    have : (M + 1 : ℝ) < (μ : ℝ) / 2 := by
      have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
      -- `2*(M+1) < μ`  =>  `M+1 < μ/2`
      -- by multiplying both sides by `1/2`.
      nlinarith
    exact this
  have hsumR' : ((Erdos.ShellStage.hazardTokensOn st).card : ℝ) + (M + 1 : ℝ) < (μ : ℝ) := by
    -- `U < μ/2` and `M+1 < μ/2`.
    nlinarith
  have hsumR : (((Erdos.ShellStage.hazardTokensOn st).card + (M + 1) : ℕ) : ℝ) < (μ : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hsumR'
  have hBcard' : st.B.card = μ := by
    simp [st, Erdos.ShellStage.mkPhaseShift, card_blockIndices]
  -- Convert back to the BlockStage inequality.
  have : st.toBlockStage.U.card + (M + 1) < μ := by
    -- `toBlockStage.U = hazardTokensOn st`
    -- and `toBlockStage.B = st.B`.
    -- Cast-then-uncast using `exact_mod_cast`.
    --
    -- (We use the real inequality `hsumR` to avoid Nat division headaches.)
    exact_mod_cast hsumR
  -- Rewrite RHS `μ` as `B.card`.
  simpa [ShellStage.toBlockStage, hBcard'] using this

end Erdos257

end Erdos
