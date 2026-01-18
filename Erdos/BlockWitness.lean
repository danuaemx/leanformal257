import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Order.WellFounded

import Erdos.TokenBijection

namespace Erdos

/--
A reusable combinatorial wrapper for the “safe block with a fresh value” step.

- `B` is the finite set of block indices.
- `U` is the finite set of hazard tokens.
- `Γ` projects a token to the block it corrupts.
- `val` assigns a *block value* to each block index.

The key structural hypothesis is that `val` is injective on `B`, which is the
formal version of “block distinctness” in the TeX.
-/
structure BlockStage (α ι β : Type) [DecidableEq α] where
  B : Finset α
  U : Finset ι
  Γ : ι → α
  val : α → β
  hΓ : ∀ u ∈ U, Γ u ∈ B
  hinj : Set.InjOn val (↑B : Set α)

namespace BlockStage

variable {α ι β : Type} [DecidableEq α]

/--
If the number of hazards plus the number of forbidden values is strictly smaller than the
number of blocks, then there exists a *safe* block whose value avoids the forbidden set.

This is the exact place where we use:
- the reversed pigeonhole lemma from `TokenBijection` (to get an un-hit block), and
- injectivity of `val` (to ensure only `S.card` blocks can map into `S`).

The output includes an explicit witness block index `b`.
-/
theorem exists_safeBlock_avoiding
    (st : BlockStage α ι β)
    (S : Finset β)
    (hcard : st.U.card + S.card < st.B.card) :
    ∃ b ∈ st.B, b ∉ st.U.image st.Γ ∧ st.val b ∉ S := by
  classical
  -- Blocks whose values land in the forbidden set.
  let T : Finset α := st.B.filter fun b => st.val b ∈ S
  have hT_subset_B : (↑T : Set α) ⊆ (↑st.B : Set α) := by
    intro b hb
    have hb' : b ∈ T := hb
    exact (Finset.mem_filter.1 hb').1
  have hinjT : Set.InjOn st.val (↑T : Set α) := st.hinj.mono hT_subset_B
  have hT_image_subset : T.image st.val ⊆ S := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨b, hbT, rfl⟩
    exact (Finset.mem_filter.1 hbT).2
  have hT_card_le : T.card ≤ S.card := by
    have hcard_image : (T.image st.val).card = T.card := by
      simpa using (Finset.card_image_of_injOn (s := T) (f := st.val) hinjT)
    have : (T.image st.val).card ≤ S.card := Finset.card_le_card hT_image_subset
    simpa [hcard_image] using this
  have hU_image_subset : st.U.image st.Γ ⊆ st.B := by
    intro b hb
    rcases Finset.mem_image.1 hb with ⟨u, huU, rfl⟩
    exact st.hΓ u huU
  -- The bad block indices are either hit by a hazard token, or map into the forbidden values.
  let Bad : Finset α := st.U.image st.Γ ∪ T
  have hBad_subset : Bad ⊆ st.B := by
    intro b hb
    rcases Finset.mem_union.1 hb with hbU | hbT
    · exact hU_image_subset hbU
    · exact (Finset.mem_filter.1 hbT).1
  have hBad_card_lt : Bad.card < st.B.card := by
    have hBad_card_le : Bad.card ≤ (st.U.image st.Γ).card + T.card := by
      simpa [Bad] using (Finset.card_union_le (st.U.image st.Γ) T)
    have hUimg_card_le : (st.U.image st.Γ).card ≤ st.U.card := Finset.card_image_le
    have hBad_card_le' : Bad.card ≤ st.U.card + S.card := by
      have : (st.U.image st.Γ).card + T.card ≤ st.U.card + S.card := by
        exact Nat.add_le_add hUimg_card_le hT_card_le
      exact le_trans hBad_card_le this
    exact lt_of_le_of_lt hBad_card_le' hcard
  have hnot_subset : ¬ st.B ⊆ Bad := by
    intro hsubset
    have hle : st.B.card ≤ Bad.card := Finset.card_le_card hsubset
    exact (not_lt_of_ge hle) hBad_card_lt
  rcases Finset.not_subset.1 hnot_subset with ⟨b, hbB, hbnotBad⟩
  have hbnotU : b ∉ st.U.image st.Γ := by
    intro hbU
    exact hbnotBad (Finset.mem_union.2 (Or.inl hbU))
  have hbnotT : b ∉ T := by
    intro hbT
    exact hbnotBad (Finset.mem_union.2 (Or.inr hbT))
  have hbval_not_mem : st.val b ∉ S := by
    intro hbval
    have : b ∈ T := by
      exact Finset.mem_filter.2 ⟨hbB, hbval⟩
    exact hbnotT this
  exact ⟨b, hbB, hbnotU, hbval_not_mem⟩

/--
A noncomputable choice of a safe block index avoiding a forbidden value set.
This is useful when you want an explicit *witness* block to define a sequence.
-/
noncomputable def chooseSafeBlock
    (st : BlockStage α ι β)
    (S : Finset β)
    (hcard : st.U.card + S.card < st.B.card) : α :=
  Classical.choose (exists_safeBlock_avoiding (st := st) (S := S) hcard)

theorem chooseSafeBlock_mem
    (st : BlockStage α ι β)
    (S : Finset β)
    (hcard : st.U.card + S.card < st.B.card) :
    chooseSafeBlock (st := st) (S := S) hcard ∈ st.B :=
  (Classical.choose_spec (exists_safeBlock_avoiding (st := st) (S := S) hcard)).1

theorem chooseSafeBlock_not_hit
    (st : BlockStage α ι β)
    (S : Finset β)
    (hcard : st.U.card + S.card < st.B.card) :
    chooseSafeBlock (st := st) (S := S) hcard ∉ st.U.image st.Γ :=
  (Classical.choose_spec (exists_safeBlock_avoiding (st := st) (S := S) hcard)).2.1

theorem chooseSafeBlock_val_not_mem
    (st : BlockStage α ι β)
    (S : Finset β)
    (hcard : st.U.card + S.card < st.B.card) :
    st.val (chooseSafeBlock (st := st) (S := S) hcard) ∉ S :=
  (Classical.choose_spec (exists_safeBlock_avoiding (st := st) (S := S) hcard)).2.2

end BlockStage

/--
If `blocks : ℕ → ℕ` is strictly increasing, then it has unbounded range in the exact sense used by
`KernelPackage.unbounded`.

This is a convenient target for the later “witness-driven block construction”: if you can build
blocks so that `StrictMono blocks` holds (with an explicit witness/selection rule), then you get
the required unboundedness immediately.
-/
theorem unbounded_of_strictMono_nat (blocks : ℕ → ℕ) (hmono : StrictMono blocks) :
    ∀ N (s : Finset ℕ), ∃ n ≥ N, blocks n ∉ s := by
  intro N s
  classical
  by_cases hs : s.Nonempty
  · let m : ℕ := s.max' hs
    let n : ℕ := max N (m + 1)
    refine ⟨n, le_max_left _ _, ?_⟩
    intro hn_mem
    have hle : blocks n ≤ m := by
      -- Any element of a nonempty finset is ≤ its `max'`.
      simpa [m] using (Finset.le_max' (s := s) (x := blocks n) hn_mem)
    have hn_le : n ≤ blocks n := (StrictMono.id_le hmono) n
    have hm_lt : m < blocks n := by
      have : m + 1 ≤ blocks n := le_trans (le_max_right N (m + 1)) hn_le
      exact lt_of_lt_of_le (Nat.lt_succ_self m) this
    exact (not_lt_of_ge hle) hm_lt
  · refine ⟨N, le_rfl, ?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.1 hs]

end Erdos
