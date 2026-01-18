import Erdos.HazardMaps
import Erdos.HazardCounting

import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card

namespace Erdos

open Finset

section Decompose

/-- A sigma-type presentation of `hazardTokens`: pick `n ∈ active`, then pick a hazardous `q`. -/
noncomputable def hazardSigma (μ L : ℕ) (M : ℕ → ℕ) (active : Finset ℕ) :
    Finset (Σ _n : ℕ, ℕ) :=
  by
    classical
    exact active.sigma (fun n => (blockIndices μ).filter (fun q => isHazard L M n q))

/-- The obvious embedding `Σ n, ℕ ↪ ℕ × ℕ`. -/
def sigmaToProdEmbedding : (Σ _n : ℕ, ℕ) ↪ ℕ × ℕ where
  toFun x := (x.1, x.2)
  inj' := by
    rintro ⟨n1, q1⟩ ⟨n2, q2⟩ h
    cases h
    rfl

theorem hazardTokens_eq_map_hazardSigma (μ L : ℕ) (M : ℕ → ℕ) (active : Finset ℕ) :
    hazardTokens μ L M active = (hazardSigma μ L M active).map sigmaToProdEmbedding := by
  classical
  ext t
  constructor
  · intro ht
    have ht0 : t ∈ (active.product (blockIndices μ)).filter (fun t => isHazard L M t.1 t.2) := by
      simpa [hazardTokens] using ht
    have ht_prod : t ∈ active.product (blockIndices μ) := (Finset.mem_filter.1 ht0).1
    have ht_haz : isHazard L M t.1 t.2 := (Finset.mem_filter.1 ht0).2
    rcases Finset.mem_product.1 ht_prod with ⟨hn, hq⟩
    -- build the sigma element and show it maps to `t`
    refine Finset.mem_map.2 ?_
    refine ⟨⟨t.1, t.2⟩, ?_, rfl⟩
    -- membership in the sigma finset
    refine Finset.mem_sigma.2 ?_
    refine ⟨hn, ?_⟩
    refine Finset.mem_filter.2 ?_
    exact ⟨hq, ht_haz⟩
  · intro ht
    rcases Finset.mem_map.1 ht with ⟨x, hx, rfl⟩
    -- `x = ⟨n,q⟩` is hazardous by sigma membership
    rcases Finset.mem_sigma.1 hx with ⟨hn, hxq⟩
    rcases Finset.mem_filter.1 hxq with ⟨hq, hhaz⟩
    -- convert to membership in `hazardTokens`
    have : (x.1, x.2) ∈ (active.product (blockIndices μ)).filter (fun t => isHazard L M t.1 t.2) := by
      refine Finset.mem_filter.2 ?_
      refine ⟨?_, hhaz⟩
      exact Finset.mem_product.2 ⟨hn, hq⟩
    simpa [hazardTokens] using this

theorem hazardTokens_card_eq_sum (μ L : ℕ) (M : ℕ → ℕ) (active : Finset ℕ) :
    (hazardTokens μ L M active).card =
      ∑ n ∈ active, ((blockIndices μ).filter (fun q => isHazard L M n q)).card := by
  classical
  -- Rewrite via sigma representation.
  have hEq := hazardTokens_eq_map_hazardSigma (μ := μ) (L := L) (M := M) (active := active)
  -- `map` preserves card.
  have hcard_map :
      ((hazardSigma μ L M active).map sigmaToProdEmbedding).card =
        (hazardSigma μ L M active).card := by
    simpa using
      (Finset.card_map (s := hazardSigma μ L M active) (f := sigmaToProdEmbedding))
  -- Compute card of the sigma finset.
  have hcard_sigma : (hazardSigma μ L M active).card =
        ∑ n ∈ active, ((blockIndices μ).filter (fun q => isHazard L M n q)).card := by
    simpa [hazardSigma] using (Finset.card_sigma (s := active)
      (t := fun n => (blockIndices μ).filter (fun q => isHazard L M n q)))
  -- Combine.
  calc
    (hazardTokens μ L M active).card
        = ((hazardSigma μ L M active).map sigmaToProdEmbedding).card := by
            simpa [hEq]
    _ = (hazardSigma μ L M active).card := hcard_map
    _ = ∑ n ∈ active, ((blockIndices μ).filter (fun q => isHazard L M n q)).card := hcard_sigma

end Decompose

section PerN

/-- A convenient membership characterization for `blockIndices` as a Nat interval. -/
theorem mem_blockIndices_iff {μ q : ℕ} : q ∈ blockIndices μ ↔ 1 ≤ q ∧ q ≤ μ := by
  constructor
  · intro h
    have h0 : q ∈ (Finset.range (μ + 1)).filter (fun q => 1 ≤ q) := by
      simpa [blockIndices] using h
    have hrange : q ∈ Finset.range (μ + 1) := (Finset.mem_filter.1 h0).1
    have hqge : 1 ≤ q := (Finset.mem_filter.1 h0).2
    have hqle : q ≤ μ := by
      -- `q < μ+1` implies `q ≤ μ`.
      exact Nat.lt_succ_iff.mp (Finset.mem_range.1 hrange)
    exact ⟨hqge, hqle⟩
  · rintro ⟨hqge, hqle⟩
    have hrange : q ∈ Finset.range (μ + 1) := by
      exact Finset.mem_range.2 (Nat.lt_succ_iff.mpr hqle)
    exact Finset.mem_filter.2 ⟨hrange, hqge⟩

/-- Casting from `{1,…,n}` into `ZMod n` is injective. -/
theorem injOn_castZMod_blockIndices (n : ℕ) [NeZero n] :
    Set.InjOn (fun q : ℕ => (q : ZMod n)) (blockIndices n : Set ℕ) := by
  classical
  intro a ha b hb hab
  have ha' := (mem_blockIndices_iff (μ := n) (q := a)).1 ha
  have hb' := (mem_blockIndices_iff (μ := n) (q := b)).1 hb
  have ha_le : a ≤ n := ha'.2
  have hb_le : b ≤ n := hb'.2
  have ha_ge : 1 ≤ a := ha'.1
  have hb_ge : 1 ≤ b := hb'.1
  have hval : (a : ZMod n).val = (b : ZMod n).val := congrArg ZMod.val hab
  -- use `val_natCast` and split by whether `a`/`b` hit the endpoint `n`.
  have hmod : a % n = b % n := by
    simpa [ZMod.val_natCast] using hval
  have ha_cases : a < n ∨ a = n := lt_or_eq_of_le ha_le
  have hb_cases : b < n ∨ b = n := lt_or_eq_of_le hb_le
  cases ha_cases with
  | inl haLt =>
      have haMod : a % n = a := Nat.mod_eq_of_lt haLt
      cases hb_cases with
      | inl hbLt =>
          have hbMod : b % n = b := Nat.mod_eq_of_lt hbLt
          exact by simpa [haMod, hbMod] using hmod
      | inr hbEq =>
          -- `b = n` forces `b % n = 0`, hence `a % n = 0`, contradiction since `a % n = a ≥ 1`.
          have h0 : a % n = 0 := by
            -- rewrite `b % n` using `hbEq`.
            simpa [hbEq] using hmod
          have : a = 0 := by
            simpa [haMod] using h0
          exact False.elim ((Nat.ne_of_gt ha_ge) this)
  | inr haEq =>
      -- `a = n` forces `a % n = 0`.
      cases hb_cases with
      | inr hbEq =>
          -- both are `n`.
          simpa [haEq, hbEq]
      | inl hbLt =>
          have hbMod : b % n = b := Nat.mod_eq_of_lt hbLt
          have h0 : b % n = 0 := by
            -- from `a % n = b % n` and `a = n`.
            simpa [haEq] using hmod.symm
          have : b = 0 := by
            simpa [hbMod] using h0
          exact False.elim ((Nat.ne_of_gt hb_ge) this)

/--
For `n` with `Nat.Coprime L n` and `M n < n`, there are at most `M n` hazardous block indices
in `{1,…,n}`.

This is the first per-`n` counting lemma: later we’ll upgrade it from `μ = n` to general `μ`.
-/
theorem card_blockIndices_filter_isHazard_le (n L : ℕ) (M : ℕ → ℕ)
    [NeZero n] (hcop : Nat.Coprime L n) (hm : M n < n) :
    ((blockIndices n).filter (fun q => isHazard L M n q)).card ≤ M n := by
  classical
  let S : Finset ℕ := (blockIndices n).filter (fun q => isHazard L M n q)
  let f : ℕ → ZMod n := fun q => (q : ZMod n)
  -- The image of `S` under casting lies in the corresponding ZMod-filter.
  have hsub : S.image f ⊆
      ((Finset.univ : Finset (ZMod n)).filter
        (fun q => 1 ≤ (q * (L : ZMod n)).val ∧ (q * (L : ZMod n)).val ≤ M n)) := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨q, hq, rfl⟩
    have hqS : q ∈ S := hq
    have hqHaz : isHazard L M n q := (Finset.mem_filter.1 hqS).2
    -- rewrite `isHazard` in ZMod terms
    have hqHaz' : 1 ≤ (q * L) % n ∧ (q * L) % n ≤ M n := by
      simpa [isHazard] using hqHaz
    have hv : ((q : ZMod n) * (L : ZMod n)).val = (q * L) % n := by
      have hmul : (q : ZMod n) * (L : ZMod n) = ((q * L : ℕ) : ZMod n) := by
        simp [Nat.cast_mul]
      -- Avoid `simp` recursion by rewriting the goal first.
      rw [hmul]
      simpa using (ZMod.val_natCast (n := n) (a := q * L))
    have : 1 ≤ ((q : ZMod n) * (L : ZMod n)).val ∧ ((q : ZMod n) * (L : ZMod n)).val ≤ M n := by
      simpa [hv] using hqHaz'
    refine Finset.mem_filter.2 ?_
    exact ⟨Finset.mem_univ _, this⟩

  -- Injectivity of cast on `S` (since `S ⊆ blockIndices n`).
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro a ha b hb hab
    have haB : a ∈ (blockIndices n : Set ℕ) := by
      have : a ∈ blockIndices n := (Finset.mem_filter.1 ha).1
      simpa using this
    have hbB : b ∈ (blockIndices n : Set ℕ) := by
      have : b ∈ blockIndices n := (Finset.mem_filter.1 hb).1
      simpa using this
    exact injOn_castZMod_blockIndices (n := n) haB hbB hab

  have hcard_image : (S.image f).card = S.card :=
    Finset.card_image_of_injOn (s := S) (f := f)
      (by
        intro a ha b hb hab
        exact hinj (by simpa using ha) (by simpa using hb) hab)

  -- Now bound by the ZMod counting lemma.
  have hZModCard :
      (((Finset.univ : Finset (ZMod n)).filter
        (fun q => 1 ≤ (q * (L : ZMod n)).val ∧ (q * (L : ZMod n)).val ≤ M n))).card = M n := by
    simpa using (card_univ_filter_val_mul_Icc_one (n := n) (L := L) (m := M n) hcop hm)

  -- `S.image f ⊆ T` gives card inequality.
  have : S.card ≤
      (((Finset.univ : Finset (ZMod n)).filter
        (fun q => 1 ≤ (q * (L : ZMod n)).val ∧ (q * (L : ZMod n)).val ≤ M n))).card := by
    -- rewrite `S.card` as `card (S.image f)` and apply `card_le_card`.
    have := Finset.card_le_card hsub
    -- `card_le_card` gives `card (S.image f) ≤ card T`.
    simpa [hcard_image] using this

  -- finalize
  simpa [S, hZModCard] using this

/--
Toy “global” bound: for a singleton active set `{n}` and `μ = n`, the hazard universe has at most
`M n` tokens (under the usual coprime and `M n < n` hypotheses).

This combines `hazardTokens_card_eq_sum` with `card_blockIndices_filter_isHazard_le`.
-/
theorem hazardTokens_card_le_M_singleton (n L : ℕ) (M : ℕ → ℕ)
    [NeZero n] (hcop : Nat.Coprime L n) (hm : M n < n) :
    (hazardTokens n L M {n}).card ≤ M n := by
  classical
  -- Expand the `hazardTokens` card as a sum over `active`.
  have hsum := hazardTokens_card_eq_sum (μ := n) (L := L) (M := M) (active := ({n} : Finset ℕ))
  -- Simplify the sum over a singleton.
  have : (hazardTokens n L M ({n} : Finset ℕ)).card =
      ((blockIndices n).filter (fun q => isHazard L M n q)).card := by
    simpa using hsum
  -- Apply the per-`n` bound.
  simpa [this] using (card_blockIndices_filter_isHazard_le (n := n) (L := L) (M := M) hcop hm)

theorem divMod_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (fun q : ℕ => (q / n, q % n)) := by
  intro a b h
  have hdiv : a / n = b / n := congrArg Prod.fst h
  have hmod : a % n = b % n := congrArg Prod.snd h
  -- Reconstruct from quotient and remainder.
  calc
    a = a / n * n + a % n := by
          simpa [Nat.mul_comm] using (Nat.div_add_mod a n).symm
    _ = b / n * n + b % n := by
          simpa [hdiv, hmod]
    _ = b := by
          simpa [Nat.mul_comm] using (Nat.div_add_mod b n)

theorem mod_mul_eq_mod_mod_mul (q L n : ℕ) (hn : 0 < n) :
    (q * L) % n = ((q % n) * L) % n := by
  -- Expand `q` into quotient/remainder and drop the multiple of `n`.
  calc
    (q * L) % n = (((q % n + n * (q / n)) * L)) % n := by
          simpa [Nat.mod_add_div q n]
    _ = (((q % n) * L + (n * (q / n)) * L)) % n := by
          simp [Nat.add_mul]
    _ = (((q % n) * L + n * ((q / n) * L))) % n := by
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = (((q % n) * L)) % n := by
          simpa using Nat.add_mul_mod_self_left ((q % n) * L) ((q / n) * L) n

theorem card_blockIndices_filter_isHazard_le_general (μ n L : ℕ) (M : ℕ → ℕ)
    [NeZero n] (hcop : Nat.Coprime L n) (hm : M n < n) :
    ((blockIndices μ).filter (fun q => isHazard L M n q)).card ≤ (μ / n + 1) * M n := by
  classical
  let S : Finset ℕ := (blockIndices μ).filter (fun q => isHazard L M n q)
  let f : ℕ → ℕ × ℕ := fun q => (q / n, q % n)
  let T : Finset ℕ := (blockIndices n).filter (fun r => isHazard L M n r)
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)

  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro a ha b hb hab
    exact divMod_injective (n := n) hnpos hab

  have hcard_image : (S.image f).card = S.card :=
    Finset.card_image_of_injOn (s := S) (f := f)
      (by
        intro a ha b hb hab
        exact hinj (by simpa using ha) (by simpa using hb) hab)

  have hsub : S.image f ⊆ (Finset.range (μ / n + 1)).product T := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨q, hqS, rfl⟩
    have hqB : q ∈ blockIndices μ := (Finset.mem_filter.1 hqS).1
    have hqHaz : isHazard L M n q := (Finset.mem_filter.1 hqS).2
    have hqB' : 1 ≤ q ∧ q ≤ μ := (mem_blockIndices_iff (μ := μ) (q := q)).1 hqB
    have hqle : q ≤ μ := hqB'.2
    have hk_le : q / n ≤ μ / n := Nat.div_le_div_right hqle
    have hk_mem : q / n ∈ Finset.range (μ / n + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le hk_le)

    have hrem_eq : (q * L) % n = ((q % n) * L) % n := mod_mul_eq_mod_mod_mul q L n hnpos
    have hqHaz' : 1 ≤ (q * L) % n ∧ (q * L) % n ≤ M n := by
      simpa [isHazard] using hqHaz
    have hremHaz : 1 ≤ ((q % n) * L) % n ∧ ((q % n) * L) % n ≤ M n := by
      refine ⟨?_, ?_⟩
      · have h1 : 1 ≤ (q * L) % n := hqHaz'.1
        -- rewrite to the remainder form (avoid `simp` recursion)
        have h1' := h1
        rw [hrem_eq] at h1'
        exact h1'
      · have h2 : (q * L) % n ≤ M n := hqHaz'.2
        have h2' := h2
        rw [hrem_eq] at h2'
        exact h2'
    have hqmod_ne : q % n ≠ 0 := by
      intro h0
      have hbad : (1 : ℕ) ≤ 0 := by
        simpa [h0] using hremHaz.1
      exact (Nat.not_succ_le_zero 0) (by simpa using hbad)

    have hqmod_ge : 1 ≤ q % n := Nat.pos_of_ne_zero hqmod_ne
    have hqmod_lt : q % n < n := Nat.mod_lt q hnpos
    have hqmod_le : q % n ≤ n := Nat.le_of_lt hqmod_lt
    have hqmod_memB : q % n ∈ blockIndices n :=
      (mem_blockIndices_iff (μ := n) (q := q % n)).2 ⟨hqmod_ge, hqmod_le⟩
    have hqmod_memT : q % n ∈ T := by
      refine Finset.mem_filter.2 ?_
      refine ⟨hqmod_memB, ?_⟩
      -- show `isHazard` for `q % n`
      have : isHazard L M n (q % n) := by
        -- `isHazard` is exactly the bounds on the remainder.
        simpa [isHazard] using hremHaz
      exact this

    exact Finset.mem_product.2 ⟨hk_mem, hqmod_memT⟩

  have hcard_le : S.card ≤ ((Finset.range (μ / n + 1)).product T).card := by
    have := Finset.card_le_card hsub
    simpa [hcard_image] using this

  have hT : T.card ≤ M n :=
    card_blockIndices_filter_isHazard_le (n := n) (L := L) (M := M) hcop hm

  -- Combine the product-card formula with the per-`n` bound.
  have hprod : ((Finset.range (μ / n + 1)).product T).card = (μ / n + 1) * T.card := by
    -- `card (range k) = k` and `card_product` gives the multiplicative formula.
    simpa using (Finset.card_product (Finset.range (μ / n + 1)) T)

  calc
    ((blockIndices μ).filter (fun q => isHazard L M n q)).card
        = S.card := by rfl
    _ ≤ ((Finset.range (μ / n + 1)).product T).card := hcard_le
    _ = (μ / n + 1) * T.card := by simpa [hprod]
    _ ≤ (μ / n + 1) * M n := Nat.mul_le_mul_left _ hT

theorem hazardTokens_card_le_sum_general (μ L : ℕ) (M : ℕ → ℕ) (active : Finset ℕ)
    (hcop : ∀ n ∈ active, Nat.Coprime L n)
    (hm : ∀ n ∈ active, M n < n)
    (hne : ∀ n ∈ active, n ≠ 0) :
    (hazardTokens μ L M active).card ≤ ∑ n ∈ active, (μ / n + 1) * M n := by
  classical
  -- Start from the exact card decomposition.
  have hsum := hazardTokens_card_eq_sum (μ := μ) (L := L) (M := M) (active := active)
  -- Prove termwise bounds and sum.
  have hle :
      (∑ n ∈ active, ((blockIndices μ).filter (fun q => isHazard L M n q)).card)
        ≤ ∑ n ∈ active, (μ / n + 1) * M n := by
    refine Finset.sum_le_sum ?_
    intro n hn
    haveI : NeZero n := ⟨hne n hn⟩
    exact card_blockIndices_filter_isHazard_le_general (μ := μ) (n := n) (L := L) (M := M)
      (hcop n hn) (hm n hn)
  -- Rewrite the LHS using `hsum`.
  simpa [hsum] using hle

end PerN

end Erdos
