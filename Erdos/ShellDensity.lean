import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Card

import Erdos.ShellStage
import Erdos.HazardTokenCard
import Erdos.ShellIrrationality

namespace Erdos

open scoped BigOperators

namespace ShellStage

/-- `hazardTokensOn st` is a subset of the full hazard universe using all block indices. -/
theorem hazardTokensOn_subset_hazardTokens (st : Erdos.ShellStage) :
    hazardTokensOn st ⊆ hazardTokens st.μ st.L st.M st.active := by
  classical
  intro t ht
  have htprod : t ∈ st.active.product st.B := (Finset.mem_filter.1 ht).1
  have htHaz : isHazard st.L st.M t.1 t.2 := (Finset.mem_filter.1 ht).2
  have ht1 : t.1 ∈ st.active := (Finset.mem_product.1 htprod).1
  have ht2B : t.2 ∈ st.B := (Finset.mem_product.1 htprod).2
  have ht2 : t.2 ∈ blockIndices st.μ := st.hB ht2B
  -- package into membership of the filtered product defining `hazardTokens`.
  refine Finset.mem_filter.2 ?_
  refine ⟨Finset.mem_product.2 ⟨ht1, ht2⟩, ?_⟩
  simpa using htHaz

/-- Card bound for `hazardTokensOn` by the already-proved global hazard bound. -/
theorem hazardTokensOn_card_le_sum_general
    (st : Erdos.ShellStage)
    (hcop : ∀ n ∈ st.active, Nat.Coprime st.L n)
    (hm : ∀ n ∈ st.active, st.M n < n)
    (hne : ∀ n ∈ st.active, n ≠ 0) :
    (hazardTokensOn st).card ≤ ∑ n ∈ st.active, (st.μ / n + 1) * st.M n := by
  classical
  have hsubset := hazardTokensOn_subset_hazardTokens st
  have hcard_le : (hazardTokensOn st).card ≤ (hazardTokens st.μ st.L st.M st.active).card :=
    Finset.card_le_card hsubset
  have hbig : (hazardTokens st.μ st.L st.M st.active).card ≤
      ∑ n ∈ st.active, (st.μ / n + 1) * st.M n :=
    hazardTokens_card_le_sum_general (μ := st.μ) (L := st.L) (M := st.M) (active := st.active)
      hcop hm hne
  exact le_trans hcard_le hbig

end ShellStage

namespace Erdos257

/--
A convenient “density-style” corollary:

If `M(n) ≤ log(n)` on the active shell and all active indices satisfy `n ≤ μ`, then
(normalizing by the block space size `μ`) the hazard-token density is controlled by the
shell log-moment, up to a harmless factor `2`.

This matches the manuscript heuristic
`|U_haz|/μ ≲ ∑_{n ∈ shell k} log(n)/n`.
-/
theorem hazardTokensOn_density_le_two_mul_shellLogMoment
    (shell : Shell) (k : ℕ) (st : Erdos.ShellStage)
    (hμ : 0 < st.μ)
    (hactive : st.active = shell k)
    (hpos : ∀ n ∈ shell k, 1 ≤ n)
    (hleμ : ∀ n ∈ shell k, n ≤ st.μ)
    (hcop : ∀ n ∈ st.active, Nat.Coprime st.L n)
    (hm : ∀ n ∈ st.active, st.M n < n)
    (hne : ∀ n ∈ st.active, n ≠ 0)
    (hMlog : ∀ n ∈ shell k, (st.M n : ℝ) ≤ Real.log (n : ℝ)) :
    ((Erdos.ShellStage.hazardTokensOn st).card : ℝ) / (st.μ : ℝ)
      ≤ 2 * shellLogMoment shell k := by
  classical
  have hμR : (0 : ℝ) < (st.μ : ℝ) := by exact_mod_cast hμ
  have hμne : (st.μ : ℝ) ≠ 0 := ne_of_gt hμR

  -- Start from the nat-card bound.
  have hcardNat : (Erdos.ShellStage.hazardTokensOn st).card ≤
      ∑ n ∈ st.active, (st.μ / n + 1) * st.M n :=
    Erdos.ShellStage.hazardTokensOn_card_le_sum_general (st := st) hcop hm hne

  -- Cast to ℝ and divide by μ.
  have hcardR : ((Erdos.ShellStage.hazardTokensOn st).card : ℝ)
      ≤ (∑ n ∈ st.active, (st.μ / n + 1) * st.M n : ℕ) := by
    exact_mod_cast hcardNat
  have hdivR : ((Erdos.ShellStage.hazardTokensOn st).card : ℝ) / (st.μ : ℝ)
      ≤ (∑ n ∈ st.active, (st.μ / n + 1) * st.M n : ℕ) / (st.μ : ℝ) :=
    (div_le_div_of_nonneg_right hcardR (le_of_lt hμR))

  -- Bound the RHS by splitting (μ/n+1) into μ/n and 1, then using `n ≤ μ` to absorb.
  have hbound_sum :
      ((∑ n ∈ st.active, (st.μ / n + 1) * st.M n : ℕ) : ℝ) / (st.μ : ℝ)
        ≤ 2 * (shellLogMoment shell k) := by
    -- Rewrite sums over `st.active` as sums over `shell k`.
    -- (avoid `subst` since `st.active` is not a variable)
    simp [hactive]
    -- We bound termwise and then sum.
    have hterm :
        ∀ n ∈ shell k,
          (((st.μ / n + 1) * st.M n : ℕ) : ℝ) / (st.μ : ℝ)
            ≤ 2 * (Real.log (n : ℝ) / (n : ℝ)) := by
      intro n hn
      have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hpos n hn)
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
      have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnR

      -- Basic bound: `(μ / n : ℝ) ≤ μ / n` (real division).
      have hdiv_cast : ((st.μ / n : ℕ) : ℝ) ≤ (st.μ : ℝ) / (n : ℝ) := by
        -- from `Nat.div_mul_le_self` and `le_div_iff`.
        have hmul_le : (st.μ / n) * n ≤ st.μ := Nat.div_mul_le_self st.μ n
        have hmul_leR : (((st.μ / n) * n : ℕ) : ℝ) ≤ (st.μ : ℝ) := by
          exact_mod_cast hmul_le
        -- `a ≤ b / c` iff `a*c ≤ b` when `0 < c`.
        -- rewrite `((st.μ / n) * n : ℝ) = ((st.μ / n : ℕ) : ℝ) * n`.
        have : ((st.μ / n : ℕ) : ℝ) * (n : ℝ) ≤ (st.μ : ℝ) := by
          simpa [Nat.cast_mul] using hmul_leR
        exact (le_div_iff₀ hnR).2 this

      have hμn1 : ((st.μ / n + 1 : ℕ) : ℝ) ≤ (st.μ : ℝ) / (n : ℝ) + 1 := by
        simpa [Nat.cast_add, Nat.cast_one] using add_le_add_right hdiv_cast 1

      -- Use `M(n) ≤ log n`.
      have hMle : (st.M n : ℝ) ≤ Real.log (n : ℝ) := hMlog n hn

      -- Convert the LHS to a product over ℝ.
      have : (((st.μ / n + 1) * st.M n : ℕ) : ℝ) / (st.μ : ℝ)
            ≤ ((st.μ : ℝ) / (n : ℝ) + 1) * (Real.log (n : ℝ)) / (st.μ : ℝ) := by
        -- First bound `(μ/n+1)` and `M` separately, then multiply.
        have hmul1 : ((st.μ / n + 1 : ℕ) : ℝ) * (st.M n : ℝ)
            ≤ ((st.μ : ℝ) / (n : ℝ) + 1) * Real.log (n : ℝ) := by
          exact mul_le_mul hμn1 hMle (by
            have : (0 : ℝ) ≤ (st.M n : ℝ) := by exact_mod_cast (Nat.zero_le _)
            exact this) (by
            have : (0 : ℝ) ≤ (st.μ : ℝ) / (n : ℝ) + 1 :=
              add_nonneg (div_nonneg (show (0 : ℝ) ≤ (st.μ : ℝ) from by exact_mod_cast (Nat.zero_le _))
                (le_of_lt hnR)) (by norm_num)
            exact this)
        -- Rewrite nat-cast product.
        have hcast : (((st.μ / n + 1) * st.M n : ℕ) : ℝ) =
            ((st.μ / n + 1 : ℕ) : ℝ) * (st.M n : ℝ) := by
          norm_cast
        -- divide by μ (positive)
        have hdiv := div_le_div_of_nonneg_right (by simpa [hcast] using hmul1) (le_of_lt hμR)
        simpa [hcast, mul_div_assoc] using hdiv

      -- Simplify the RHS and absorb the `+1` term using `n ≤ μ`.
      -- We only need an upper bound by `2 * log(n)/n`.
      have hleμ' : (n : ℝ) ≤ (st.μ : ℝ) := by exact_mod_cast (hleμ n hn)
      have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (hpos n hn)
        simpa using Real.log_nonneg this
      have hone_over_μ_le_one_over_n : (Real.log (n : ℝ)) / (st.μ : ℝ) ≤ (Real.log (n : ℝ)) / (n : ℝ) := by
        -- since `0 ≤ log n` and `n ≤ μ`.
        have : (1 / (st.μ : ℝ)) ≤ (1 / (n : ℝ)) := by
          -- from `n ≤ μ` we get `1/μ ≤ 1/n`.
          have hnRpos : 0 < (n : ℝ) := hnR
          have : (n : ℝ) ≤ (st.μ : ℝ) := hleμ'
          simpa [one_div] using (one_div_le_one_div_of_le hnRpos this)
        -- multiply by nonnegative log.
        simpa [div_eq_mul_inv, one_div] using (mul_le_mul_of_nonneg_left this hlog_nonneg)

      have hmain_eq : ((st.μ : ℝ) / (n : ℝ) + 1) * Real.log (n : ℝ) / (st.μ : ℝ)
          = (Real.log (n : ℝ)) / (n : ℝ) + (Real.log (n : ℝ)) / (st.μ : ℝ) := by
        -- algebra: (μ/n + 1) * log / μ = log/n + log/μ
        field_simp [hμne, hnRne]

      have hmain : ((st.μ : ℝ) / (n : ℝ) + 1) * Real.log (n : ℝ) / (st.μ : ℝ)
          ≤ (Real.log (n : ℝ)) / (n : ℝ) + (Real.log (n : ℝ)) / (st.μ : ℝ) := by
        simpa [hmain_eq]

      have htwo : (Real.log (n : ℝ)) / (n : ℝ) + (Real.log (n : ℝ)) / (st.μ : ℝ)
          ≤ 2 * (Real.log (n : ℝ) / (n : ℝ)) := by
        -- use `log/μ ≤ log/n`.
        have : (Real.log (n : ℝ)) / (st.μ : ℝ) ≤ (Real.log (n : ℝ)) / (n : ℝ) :=
          hone_over_μ_le_one_over_n
        nlinarith

      exact le_trans (le_trans this hmain) htwo

    -- Sum the termwise bounds (in the simp-normal form for casts).
    have hsum :
        (∑ n ∈ shell k, (((((st.μ / n : ℕ) : ℝ) + 1) * (st.M n : ℝ)) / (st.μ : ℝ)))
          ≤ ∑ n ∈ shell k, 2 * (Real.log (n : ℝ) / (n : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have ht := hterm n hn
      -- put `ht` into the same simp-normal form as the sum.
      simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using ht

    -- Pull out the constant 2 and recognize `shellLogMoment`.
    have hsum2 : (∑ n ∈ shell k, 2 * (Real.log (n : ℝ) / (n : ℝ)))
        = 2 * shellLogMoment shell k := by
      simp [shellLogMoment, Finset.mul_sum]

    -- Distribute the outer `/μ` across the sum.
    have hdist :
        (∑ n ∈ shell k, (((st.μ / n : ℕ) : ℝ) + 1) * (st.M n : ℝ)) / (st.μ : ℝ)
          = ∑ n ∈ shell k, ((((st.μ / n : ℕ) : ℝ) + 1) * (st.M n : ℝ)) / (st.μ : ℝ) := by
      simp [div_eq_mul_inv, Finset.sum_mul]

    -- Finish.
    calc
      (∑ n ∈ shell k, (((st.μ / n : ℕ) : ℝ) + 1) * (st.M n : ℝ)) / (st.μ : ℝ)
          = ∑ n ∈ shell k, ((((st.μ / n : ℕ) : ℝ) + 1) * (st.M n : ℝ)) / (st.μ : ℝ) :=
            hdist
      _ ≤ ∑ n ∈ shell k, 2 * (Real.log (n : ℝ) / (n : ℝ)) := hsum
      _ = 2 * shellLogMoment shell k := hsum2

  exact le_trans hdivR hbound_sum

end Erdos257

end Erdos
