import Erdos.ShellStage
import Erdos.HazardTokenCard

namespace Erdos

/-!
### Concrete perturbation-block lists

The generalized-carry concatenation `concatWithCarryTrace/Blocks` is parameterized by
- a fixed `baseBlock`, and
- a list of perturbation blocks `ps = [p₁, …, p_K]`.

In the manuscript these perturbation blocks are denoted `B_{N+1,q}` for `q = 1,…,K`.

In this repo we often have a *block-value function* `val : ℕ → ℕ` (e.g. coming from a stage
construction), and we want to turn it into the canonical list `[val 1, …, val K]`.

This file defines that list, plus small length simp-lemmas that make it easy to plug into the
existing generalized-carry pipeline.
-/

/-- The canonical list of block indices `[1,2,…,K]`. -/
def blockIndexList (K : ℕ) : List ℕ :=
  (List.range K).map (fun i => i + 1)

@[simp] theorem blockIndexList_length (K : ℕ) : (blockIndexList K).length = K := by
  simp [blockIndexList]

/-- Turn a block-value function `q ↦ val q` into the perturbation list `[val 1, …, val K]`. -/
def perturbBlocksOfVal (K : ℕ) (val : ℕ → ℕ) : List ℕ :=
  (blockIndexList K).map val

@[simp] theorem perturbBlocksOfVal_length (K : ℕ) (val : ℕ → ℕ) :
    (perturbBlocksOfVal K val).length = K := by
  simp [perturbBlocksOfVal]

namespace ShellStage

/-- The full perturbation list for a stage: `[st.val 1, …, st.val st.μ]`. -/
def perturbBlocks (st : Erdos.ShellStage) : List ℕ :=
  perturbBlocksOfVal st.μ st.val

@[simp] theorem perturbBlocks_length (st : Erdos.ShellStage) : st.perturbBlocks.length = st.μ := by
  simp [ShellStage.perturbBlocks]

end ShellStage

end Erdos
