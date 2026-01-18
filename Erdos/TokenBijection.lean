import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace Erdos

/--
### Token / bijection argument (reversed pigeonhole)

This file formalizes the combinatorial counting step used in the manuscript around
“Carry Interference Tokens” and the “Bijective Exhaustion Assumption”:

- You have a finite set of blocks `B`.
- You have a finite set of “hazard tokens” `U`.
- A projection `Γ` assigns each token to the block it corrupts.

If every token lands in `B` and `card U < card B`, then **some block is not hit by any token**.

Note this lemma does *not* formalize the analytic bound that `card U < card B`; it only
provides the deterministic pigeonhole step once that inequality is available.
-/
theorem exists_block_not_hit_of_card_tokens_lt
    {α ι : Type} [DecidableEq α]
    (B : Finset α) (U : Finset ι) (Γ : ι → α)
    (hΓ : ∀ u ∈ U, Γ u ∈ B)
    (hcard : U.card < B.card) :
    ∃ b ∈ B, b ∉ U.image Γ := by
  classical
  have himage_subset : U.image Γ ⊆ B := by
    intro b hb
    rcases Finset.mem_image.1 hb with ⟨u, huU, rfl⟩
    exact hΓ u huU
  have hcard_image : (U.image Γ).card < B.card := by
    have : (U.image Γ).card ≤ U.card := Finset.card_image_le
    exact lt_of_le_of_lt this hcard
  have hnot_subset : ¬ B ⊆ U.image Γ := by
    intro hsubset
    have hle : B.card ≤ (U.image Γ).card := Finset.card_le_card hsubset
    exact (not_lt_of_ge hle) hcard_image
  rcases Finset.not_subset.1 hnot_subset with ⟨b, hbB, hbnot⟩
  exact ⟨b, hbB, hbnot⟩

end Erdos
