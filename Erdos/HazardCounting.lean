import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace Erdos

open Finset

section ZModIntervalCounts

variable {n : ℕ} [NeZero n]

/--
For `m < n`, the finset of elements of `ZMod n` whose `val` lies in `[1,m]` has cardinality `m`.

This is the basic "interval in residues" counting fact that later drives the hazard-token bounds.
-/
theorem card_univ_filter_val_Icc_one (m : ℕ) (hm : m < n) :
    ((Finset.univ : Finset (ZMod n)).filter (fun x => 1 ≤ x.val ∧ x.val ≤ m)).card = m := by
  classical
  -- Identify the filtered set with the image of the Nat interval `[1,m]` under `Nat.cast`.
  have hEq :
      ((Finset.Icc (1 : ℕ) m).image (fun r : ℕ => (r : ZMod n))) =
        ((Finset.univ : Finset (ZMod n)).filter (fun x => 1 ≤ x.val ∧ x.val ≤ m)) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.1 hx with ⟨r, hr, rfl⟩
      have hrn : r < n := lt_of_le_of_lt (Finset.mem_Icc.1 hr).2 hm
      have : (r : ZMod n).val = r := ZMod.val_natCast_of_lt hrn
      refine Finset.mem_filter.2 ?_
      constructor
      · simpa using (Finset.mem_univ (r : ZMod n))
      · simpa [this] using (Finset.mem_Icc.1 hr)
    · intro hx
      have hx' := Finset.mem_filter.1 hx
      have hxval : 1 ≤ x.val ∧ x.val ≤ m := hx'.2
      refine Finset.mem_image.2 ?_
      refine ⟨x.val, ?_, ?_⟩
      · exact Finset.mem_Icc.2 hxval
      · -- `x = x.val` in `ZMod n`.
        simpa using (ZMod.natCast_zmod_val x).symm

  -- Show the Nat-cast map is injective on `[1,m]` using `m < n`.
  have hinj : Set.InjOn (fun r : ℕ => (r : ZMod n)) (Set.Icc (1 : ℕ) m) := by
    intro r hr s hs hrs
    have hrn : r < n := lt_of_le_of_lt hr.2 hm
    have hsn : s < n := lt_of_le_of_lt hs.2 hm
    have hvals : (r : ZMod n).val = (s : ZMod n).val := congrArg ZMod.val hrs
    -- `val` recovers the original nat when `< n`.
    simpa [ZMod.val_natCast_of_lt hrn, ZMod.val_natCast_of_lt hsn] using hvals

  have hcardIcc : (Finset.Icc (1 : ℕ) m).card = m := by
    -- `Nat.card_Icc` is a simp lemma for Nat intervals.
    simpa using (Nat.card_Icc (a := (1 : ℕ)) (b := m))

  -- Convert via the image cardinality.
  have :
      (((Finset.Icc (1 : ℕ) m).image (fun r : ℕ => (r : ZMod n))).card) = m := by
    have himage :
        ((Finset.Icc (1 : ℕ) m).image (fun r : ℕ => (r : ZMod n))).card =
          (Finset.Icc (1 : ℕ) m).card :=
      Finset.card_image_of_injOn (s := Finset.Icc (1 : ℕ) m) (f := fun r : ℕ => (r : ZMod n))
        (by
          intro a ha b hb hab
          have ha' : a ∈ Set.Icc (1 : ℕ) m := by
            simpa using ha
          have hb' : b ∈ Set.Icc (1 : ℕ) m := by
            simpa using hb
          exact hinj ha' hb' hab)
    simpa [hcardIcc] using himage

  -- Rewrite the goal using the identified finsets.
  simpa [hEq] using this

/--
If `Nat.Coprime L n`, then multiplication by `L` permutes residues modulo `n`.
Consequently the number of residues whose product lands in `[1,m]` is exactly `m`
(as long as `m < n`).
-/
theorem card_univ_filter_val_mul_Icc_one (L m : ℕ)
    (hcop : Nat.Coprime L n) (hm : m < n) :
    ((Finset.univ : Finset (ZMod n)).filter
        (fun q => 1 ≤ (q * (L : ZMod n)).val ∧ (q * (L : ZMod n)).val ≤ m)).card = m := by
  classical
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime L hcop
  let p : Equiv.Perm (ZMod n) := u.mulRight
  -- Reduce to the previous lemma by using the permutation invariance of cardinality.
  have hperm :
      ((Finset.univ : Finset (ZMod n)).filter (fun q => 1 ≤ (p q).val ∧ (p q).val ≤ m)).card =
        ((Finset.univ : Finset (ZMod n)).filter (fun q => 1 ≤ q.val ∧ q.val ≤ m)).card := by
    -- Map the left-hand filtered set along the permutation; membership is preserved by design.
    have hmap :
        ((Finset.univ : Finset (ZMod n)).filter (fun q => 1 ≤ (p q).val ∧ (p q).val ≤ m)).map
            p.toEmbedding =
          ((Finset.univ : Finset (ZMod n)).filter (fun q => 1 ≤ q.val ∧ q.val ≤ m)) := by
      ext y
      -- `mem_map_equiv` rewrites membership in `map` via `p.symm`.
      simp [Finset.mem_map_equiv, p]
    -- `map` along an embedding preserves cardinality.
    have hcard := (Finset.card_map (f := p.toEmbedding)
      (s := (Finset.univ : Finset (ZMod n)).filter (fun q => 1 ≤ (p q).val ∧ (p q).val ≤ m)))
    -- Rearrange and rewrite by `hmap`.
    simpa [hmap] using hcard.symm

  have hbase := card_univ_filter_val_Icc_one (n := n) (m := m) hm

  -- `p` is right-multiplication by the unit corresponding to `L`.
  have hmul :
      ((Finset.univ : Finset (ZMod n)).filter
          (fun q => 1 ≤ (p q).val ∧ (p q).val ≤ m)) =
        ((Finset.univ : Finset (ZMod n)).filter
          (fun q => 1 ≤ (q * (L : ZMod n)).val ∧ (q * (L : ZMod n)).val ≤ m)) := by
    ext q
    simp [p, u, ZMod.coe_unitOfCoprime]

  -- Put everything together.
  calc
    ((Finset.univ : Finset (ZMod n)).filter
          (fun q => 1 ≤ (q * (L : ZMod n)).val ∧ (q * (L : ZMod n)).val ≤ m)).card
        = ((Finset.univ : Finset (ZMod n)).filter
          (fun q => 1 ≤ (p q).val ∧ (p q).val ≤ m)).card := by
          simpa [hmul]
    _ = ((Finset.univ : Finset (ZMod n)).filter (fun q => 1 ≤ q.val ∧ q.val ≤ m)).card := hperm
    _ = m := hbase

end ZModIntervalCounts

end Erdos
