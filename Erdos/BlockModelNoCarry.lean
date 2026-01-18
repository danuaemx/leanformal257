import Erdos.Basic

namespace Erdos

namespace BlockModel

/-!
### “No carry enters” helper lemmas

These are small arithmetic facts about `concatWithCarryTrace` that correspond to the manuscript’s
boundary conditions (notably `\kappa_K = 0`) and the local slogan “this block is carry-free”.
-/

/-- The last carry in the carry trace is always `0` (the initialization `κ_K = 0`). -/
theorem concatWithCarryTrace_carries_get_last_eq_zero
  (b L baseBlock : ℕ) (ps : List ℕ) :
  let carries := (concatWithCarryTrace b L baseBlock ps).2.2
  carries[ps.length]'
    (by
      have hc : carries.length = ps.length + 1 :=
      concatWithCarryTrace_carries_length (b := b) (L := L) (baseBlock := baseBlock) ps
      -- `ps.length < carries.length`.
      simpa [hc] using Nat.lt_succ_self ps.length)
    = 0 := by
  induction ps with
  | nil =>
    simp [concatWithCarryTrace]
  | cons p ps ih =>
    -- Unfold one step of the trace; the carry list is `κ' :: carriesTail`.
    -- The last element is the last element of `carriesTail`.
    simp [concatWithCarryTrace_cons, ih]

/--
If the incoming carry into a block is zero, then the output block is just the naive sum reduced
modulo the block base.

This is the Lean analogue of the manuscript slogan “no carry enters this block, so the block is
cleanly aligned”.
-/
theorem concatWithCarryBlocks_get_of_carryNext_eq_zero
    (b L baseBlock : ℕ) (ps : List ℕ) (i : Fin ps.length)
    (hnext :
      let carries := (concatWithCarryTrace b L baseBlock ps).2.2
      carries[i.1 + 1]'
          (by
            have hc : carries.length = ps.length + 1 :=
              concatWithCarryTrace_carries_length (b := b) (L := L) (baseBlock := baseBlock) ps
            -- `i.1 + 1 < carries.length`.
            simpa [hc] using Nat.succ_lt_succ i.isLt) = 0) :
    (concatWithCarryBlocks b L baseBlock ps).get
        ⟨i.1, by
          have hl : (concatWithCarryBlocks b L baseBlock ps).length = ps.length :=
            concatWithCarryBlocks_length (b := b) (L := L) (baseBlock := baseBlock) ps
          simp [hl]⟩
      = (baseBlock + ps.get i) % blockBase b L := by
  classical
  -- Start from the per-index block recurrence and simplify the carry term.
  -- Unfold the `let`-bindings in both the recurrence and `hnext`.
  have h :=
    concatWithCarryBlocks_get (b := b) (L := L) (baseBlock := baseBlock) (ps := ps) i
  -- `simp` with `hnext` kills the carry term; remaining goal is reassociating `+`.
  -- (The recurrence is stated as `baseBlock + ps.get i + carryNext`, but simp may rewrite as
  -- `baseBlock + (ps.get i + carryNext)`.)
  simpa [hnext, Nat.add_assoc] using h

/--
The last output block is always “clean” because the carry trace is initialized with `κ_K = 0`.

This is the exact formal content of the manuscript’s boundary condition for the generalized-carry
concatenation.
-/
theorem concatWithCarryBlocks_get_last
    (b L baseBlock : ℕ) (ps : List ℕ) (hps : 0 < ps.length) :
    let i : Fin ps.length := ⟨ps.length - 1, Nat.sub_lt hps Nat.one_pos⟩
    (concatWithCarryBlocks b L baseBlock ps).get
        ⟨i.1, by
          have hl : (concatWithCarryBlocks b L baseBlock ps).length = ps.length :=
            concatWithCarryBlocks_length (b := b) (L := L) (baseBlock := baseBlock) ps
          simpa [hl] using i.isLt⟩
      = (baseBlock + ps.get i) % blockBase b L := by
  classical
  intro i
  -- Apply the general “no incoming carry” lemma at the last index.
  refine
    concatWithCarryBlocks_get_of_carryNext_eq_zero (b := b) (L := L) (baseBlock := baseBlock)
      (ps := ps) i ?_
  -- The “next carry” for the last block is the last carry in the trace, which is `0`.
  have hi : i.1 + 1 = ps.length := by
    -- `i.1 = ps.length - 1`, so `i.1 + 1 = ps.length` since `ps.length > 0`.
    simpa [i, Nat.sub_add_cancel (Nat.succ_le_of_lt hps)]
  simpa [hi] using
    (concatWithCarryTrace_carries_get_last_eq_zero (b := b) (L := L) (baseBlock := baseBlock)
      (ps := ps))

end BlockModel

end Erdos
