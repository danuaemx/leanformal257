import Mathlib.Data.ZMod.Basic
import Erdos.HazardMaps
import Erdos.HazardTokenCard

namespace Erdos

/--
The manuscript’s “phase shift” map for a modulus `n` and background period length `L`.

For a block index `q`, the injected position is the residue class of `q·L` modulo `n`.
We model this canonically in `ZMod n`.
-/
noncomputable def phaseShiftZMod (n L : ℕ) : ℕ → ZMod n :=
  fun q => (q : ZMod n) * (L : ZMod n)

/--
Phase shift injectivity (CRT-style): if `gcd(L,n)=1`, then the map `q ↦ q·L (mod n)` is injective
on the manuscript block-index set `{1,…,n}`.

This is the Lean core of the manuscript’s Proposition “Injectivity of the Phase Shift” when the
local modulus `n` is coprime to the background period `L`.
-/
theorem phaseShiftZMod_injOn_blockIndices (n L : ℕ) [NeZero n] (hcop : Nat.Coprime L n) :
    Set.InjOn (phaseShiftZMod n L) (blockIndices n : Set ℕ) := by
  classical
  intro a ha b hb hab
  -- Turn `L` into a unit modulo `n`.
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime L hcop
  have hu : (u : ZMod n) = (L : ZMod n) := by
    simp [u]
  -- Cancel the unit factor on the right.
  have hab' : (a : ZMod n) = (b : ZMod n) := by
    -- Rewrite the hypothesis using `u`.
    have habu : (a : ZMod n) * (u : ZMod n) = (b : ZMod n) * (u : ZMod n) := by
      simpa [phaseShiftZMod, hu] using hab
    -- Multiply by `u⁻¹` on the right.
    have habu' : ((a : ZMod n) * (u : ZMod n)) * (↑(u⁻¹) : ZMod n) =
        ((b : ZMod n) * (u : ZMod n)) * (↑(u⁻¹) : ZMod n) :=
      congrArg (fun x : ZMod n => x * (↑(u⁻¹) : ZMod n)) habu
    -- Simplify both sides.
    -- `u * u⁻¹ = 1` in the units, hence also in `ZMod n`.
    simpa [mul_assoc] using habu'
  -- Convert equality in `ZMod n` back to equality of naturals on `blockIndices n`.
  have hinjNat := injOn_castZMod_blockIndices (n := n)
  exact hinjNat ha hb hab'

/--
A remainder-valued version of the phase shift: the canonical representative in `{0,…,n-1}`.

This corresponds to the manuscript’s notation `z_q = (q·L) mod n`.
-/
noncomputable def phaseShiftNat (n L : ℕ) [NeZero n] : ℕ → ℕ :=
  fun q => (phaseShiftZMod n L q).val

/--
Phase shift injectivity, as a statement about remainders in `ℕ`.

Because `ZMod.val` is injective, this is an immediate corollary of
`phaseShiftZMod_injOn_blockIndices`.
-/
theorem phaseShiftNat_injOn_blockIndices (n L : ℕ) [NeZero n] (hcop : Nat.Coprime L n) :
    Set.InjOn (phaseShiftNat n L) (blockIndices n : Set ℕ) := by
  classical
  intro a ha b hb hab
  have hinjZ : Set.InjOn (phaseShiftZMod n L) (blockIndices n : Set ℕ) :=
    phaseShiftZMod_injOn_blockIndices (n := n) (L := L) hcop
  -- Injectivity of `val` on all of `ZMod n`.
  have hvalinj : Function.Injective (ZMod.val : ZMod n → ℕ) := ZMod.val_injective n
  -- First upgrade equality of `val`s to equality in `ZMod n`.
  have hz : phaseShiftZMod n L a = phaseShiftZMod n L b := by
    exact hvalinj hab
  -- Then use the ZMod-level injectivity.
  exact hinjZ ha hb hz

/--
Restrict phase shift injectivity from the full block-index set `{1,…,n}` to any finite subset.

This is the typical form needed to provide the `hinj` field of a `ShellStage` when you already
know `B ⊆ blockIndices n`.
-/
theorem phaseShiftNat_injOn_of_subset_blockIndices
    (n L : ℕ) [NeZero n] (hcop : Nat.Coprime L n)
    (B : Finset ℕ) (hB : B ⊆ blockIndices n) :
    Set.InjOn (phaseShiftNat n L) (↑B : Set ℕ) := by
  classical
  intro a ha b hb hab
  have ha' : a ∈ (blockIndices n : Set ℕ) := by
    -- `ha : a ∈ (↑B : Set ℕ)` is definitionaly `a ∈ B`.
    exact hB (by simpa using ha)
  have hb' : b ∈ (blockIndices n : Set ℕ) := by
    exact hB (by simpa using hb)
  exact (phaseShiftNat_injOn_blockIndices (n := n) (L := L) hcop) ha' hb' hab

/-!
### CRT projection to the local `P`-part

The manuscript uses a factorization `n⋆ = M·P`, where only the “local” modulus `P` is coprime to
the background period `L`.

We model the canonical projection `π_P : ZMod (M·P) → ZMod P` using `ZMod.castHom` and show that
phase shifting commutes with this projection. This lets us recover injectivity of the phase shift
*modulo the `P`-part* under the weaker hypothesis `Nat.Coprime L P`.
-/

/-- The canonical projection `π_P : ℤ/(M·P) → ℤ/P` (since `P ∣ M·P`). -/
noncomputable def projP (M P : ℕ) : ZMod (M * P) →+* ZMod P :=
  ZMod.castHom (by
      -- `P ∣ M*P`.
      simpa [Nat.mul_comm] using (Nat.dvd_mul_left P M)) (ZMod P)

/-- Phase shift commutes with the CRT projection to the `P`-part. -/
theorem projP_phaseShiftZMod
    (M P L q : ℕ) :
    projP M P (phaseShiftZMod (M * P) L q) = phaseShiftZMod P L q := by
  classical
  -- `ZMod.castHom` respects casts from `ℕ` and multiplication.
  simp [projP, phaseShiftZMod]

/--
Injectivity of the phase shift *modulo the `P`-part*.

This is the Lean analogue of the manuscript’s Proposition “Injectivity of the Phase Shift” in the
general (non-coprime) case `n⋆ = M·P`, using only the local coprimality `gcd(L,P)=1`.
-/
theorem phaseShiftZMod_injOn_blockIndices_PPart
    (M P L : ℕ) [NeZero P] (hcop : Nat.Coprime L P) :
    Set.InjOn (fun q => projP M P (phaseShiftZMod (M * P) L q)) (blockIndices P : Set ℕ) := by
  classical
  intro a ha b hb hab
  -- Rewrite the hypothesis through the commuting lemma.
  have hab' : phaseShiftZMod P L a = phaseShiftZMod P L b := by
    simpa [projP_phaseShiftZMod] using hab
  -- Apply the already-proved coprime injectivity at modulus `P`.
  exact (phaseShiftZMod_injOn_blockIndices (n := P) (L := L) hcop) ha hb hab'

/-- A remainder-valued version of the `P`-part phase shift. -/
noncomputable def phaseShiftNatPPart (M P L : ℕ) [NeZero P] : ℕ → ℕ :=
  fun q => (projP M P (phaseShiftZMod (M * P) L q)).val

/-- The `P`-part remainder is exactly the phase shift modulo `P`. -/
theorem phaseShiftNatPPart_eq_phaseShiftNat
    (M P L q : ℕ) [NeZero P] :
    phaseShiftNatPPart M P L q = phaseShiftNat P L q := by
  classical
  simp [phaseShiftNatPPart, phaseShiftNat, projP_phaseShiftZMod]

/-- Injectivity of the `P`-part phase shift on `{1,…,P}` under `Nat.Coprime L P`. -/
theorem phaseShiftNatPPart_injOn_blockIndices
    (M P L : ℕ) [NeZero P] (hcop : Nat.Coprime L P) :
    Set.InjOn (phaseShiftNatPPart M P L) (blockIndices P : Set ℕ) := by
  classical
  -- Reduce to `phaseShiftNat` using the pointwise equality.
  intro a ha b hb hab
  have hab' : phaseShiftNat P L a = phaseShiftNat P L b := by
    -- rewrite both sides via the definitional equality
    simpa [phaseShiftNatPPart_eq_phaseShiftNat (M := M) (P := P) (L := L)] using hab
  exact (phaseShiftNat_injOn_blockIndices (n := P) (L := L) hcop) ha hb hab'

/-- Monotonicity of the manuscript block-index set: `{1,…,P} ⊆ {1,…,μ}` if `P ≤ μ`. -/
theorem blockIndices_subset_blockIndices {P μ : ℕ} (h : P ≤ μ) :
    blockIndices P ⊆ blockIndices μ := by
  classical
  intro q hq
  have hq' : 1 ≤ q ∧ q ≤ P := (mem_blockIndices_iff (μ := P) (q := q)).1 hq
  exact (mem_blockIndices_iff (μ := μ) (q := q)).2 ⟨hq'.1, le_trans hq'.2 h⟩

/--
Manuscript-friendly wrapper: if the stage length `μ` satisfies `μ ≥ P`, then the `P`-part phase
shift is injective on the first `P` blocks *viewed as a subset* of `blockIndices μ`.

Formally this packages:
- the injectivity on `blockIndices P`, and
- the inclusion `blockIndices P ⊆ blockIndices μ`.
-/
theorem phaseShiftNatPPart_injOn_firstP_as_subset
    (M μ P L : ℕ) [NeZero P] (hcop : Nat.Coprime L P) (hPμ : P ≤ μ) :
    Set.InjOn (phaseShiftNatPPart M P L) (blockIndices P : Set ℕ) ∧
      (blockIndices P ⊆ blockIndices μ) := by
  refine ⟨phaseShiftNatPPart_injOn_blockIndices (M := M) (P := P) (L := L) hcop, ?_⟩
  exact blockIndices_subset_blockIndices (P := P) (μ := μ) hPμ

end Erdos
