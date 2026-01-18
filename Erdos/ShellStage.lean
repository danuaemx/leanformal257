import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

import Erdos.BlockWitness
import Erdos.HazardMaps

namespace Erdos

/--
A *single shell stage* (the `k`-th step in the manuscript), packaged in a way that plugs into the
formal token/bijection kernel.

Key points:
- `B` is the finite set of **suitable block indices** (the allowed `q` values).
- `U` is the finite set of **hazard tokens** restricted to those `q ∈ B`.
- `Γ` maps a token to the block index it corrupts.
- `witness` is the chosen witness term `n⋆` (maximal valuation / phase-shift term).
- `val` assigns an integer **block value** to each block index.
- `hinj` is the formal “distinct blocks” statement: `val` is injective on `B`.

This file does **not** prove `hinj`; it records it as the exact point where the witness-term
argument (CRT / phase shift) must be formalized.
-/
structure ShellStage where
  /-- Total number of blocks in the period space. -/
  μ : ℕ
  /-- Background period length (manuscript: `L_{k-1}`). -/
  L : ℕ
  /-- Active terms in the current shell/layer. -/
  active : Finset ℕ
  /-- Carry displacement bound `M(n)` (depends on the term). -/
  M : ℕ → ℕ
  /-- The finite set of *allowed* block indices (suitable `q` values). -/
  B : Finset ℕ
  /-- Sanity: allowed indices live in `{1,…,μ}`. -/
  hB : B ⊆ blockIndices μ
  /-- Witness term `n⋆` (chosen from the active set). -/
  witness : ℕ
  hwitness : witness ∈ active
  /-- Integer block value extracted at block index `q`. -/
  val : ℕ → ℕ
  /-- Distinctness: `val` is injective on the allowed block indices. -/
  hinj : Set.InjOn val (↑B : Set ℕ)

namespace ShellStage

/-- Hazard tokens restricted to the suitable `q` values. -/
noncomputable def hazardTokensOn (st : ShellStage) : Finset (ℕ × ℕ) := by
  classical
  exact (st.active.product st.B).filter (fun t => isHazard st.L st.M t.1 t.2)

/-- The projection `Γ` sending a token to its (corrupted) block index. -/
def Γ : (ℕ × ℕ) → ℕ := Gamma

theorem Γ_mem_B {st : ShellStage} {t : ℕ × ℕ} (ht : t ∈ hazardTokensOn st) :
    Γ t ∈ st.B := by
  classical
  have ht' : t ∈ st.active.product st.B := (Finset.mem_filter.1 ht).1
  exact (Finset.mem_product.1 ht').2

/--
Convert a `ShellStage` into the generic `BlockStage` used by the token/witness machinery.

This is the adapter that lets you reuse lemmas from:
- [Erdos/TokenBijection.lean](Erdos/TokenBijection.lean)
- [Erdos/BlockWitness.lean](Erdos/BlockWitness.lean)
- [Erdos/TokenKernelBridge.lean](Erdos/TokenKernelBridge.lean)
-/
noncomputable def toBlockStage (st : ShellStage) : BlockStage ℕ (ℕ × ℕ) ℕ :=
  { B := st.B
    U := hazardTokensOn st
    Γ := Γ
    val := st.val
    hΓ := by
      intro u hu
      exact Γ_mem_B (st := st) (t := u) hu
    hinj := st.hinj }

end ShellStage

end Erdos
