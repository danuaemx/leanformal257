import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

import Erdos.BlockWitness

namespace Erdos

/--
A family of “block stages”, indexed by a natural parameter `k`.

This is the abstract skeleton behind the TeX’s shell-step construction:
for each `k` you have
- a finite set of block indices `B_k`,
- a finite set of hazard tokens `U_k` and a projection `Γ_k : U_k → B_k`, and
- a value map `val_k` from block index to an integer block value,
  assumed injective on `B_k` (block distinctness).

No analytic estimates are encoded here; those appear only via the `surplus` hypothesis below.
-/
structure StageFamily where
  stage : ℕ → BlockStage ℕ ℕ ℕ

namespace StageFamily

open BlockStage

/--
Surplus hypothesis: for any target threshold `M`, there exists some stage `k` with enough
available blocks to beat both
- the number of hazard tokens at that stage, and
- a forbidden initial segment of size `M+1`.

This is a clean combinatorial proxy for “token density tends to 0 while `|B_k|` grows”.
-/
def HasSurplus (F : StageFamily) : Prop :=
  ∀ M : ℕ, ∃ k : ℕ, (F.stage k).U.card + (M + 1) < (F.stage k).B.card

noncomputable def chooseStage (F : StageFamily) (h : HasSurplus F) (M : ℕ) : ℕ :=
  Classical.choose (h M)

theorem chooseStage_spec (F : StageFamily) (h : HasSurplus F) (M : ℕ) :
    (F.stage (chooseStage F h M)).U.card + (M + 1) < (F.stage (chooseStage F h M)).B.card :=
  Classical.choose_spec (h M)

/--
A *witnessed* block-value sequence built from a stage family.

At each step, we choose a stage large enough to avoid the initial segment `0..M`, where
`M` is the previously chosen value; injectivity ensures we do not “waste” too many blocks.

This makes the resulting sequence strictly increasing, hence unbounded.
-/
noncomputable def blocks (F : StageFamily) (h : HasSurplus F) : ℕ → ℕ
  | 0 =>
      let k := chooseStage F h 0
      let st := F.stage k
      let S : Finset ℕ := Finset.range 1
      let hcard : st.U.card + S.card < st.B.card := by
        simpa [S, Finset.card_range] using (chooseStage_spec F h 0)
      st.val (chooseSafeBlock (st := st) (S := S) hcard)
  | n + 1 =>
      let prev := blocks F h n
      let k := chooseStage F h prev
      let st := F.stage k
      let S : Finset ℕ := Finset.range (prev + 1)
      let hcard : st.U.card + S.card < st.B.card := by
        simpa [S, Finset.card_range] using (chooseStage_spec F h prev)
      st.val (chooseSafeBlock (st := st) (S := S) hcard)

/-- The sequence `blocks` is strictly increasing. -/
theorem strictMono_blocks (F : StageFamily) (h : HasSurplus F) : StrictMono (blocks F h) := by
  classical
  -- It suffices to prove `blocks n < blocks (n+1)` for all `n`.
  refine strictMono_nat_of_lt_succ (f := blocks F h) (fun n => ?_)
  set prev : ℕ := blocks F h n with hprev
  set k : ℕ := chooseStage F h prev with hk
  set st : BlockStage ℕ ℕ ℕ := F.stage k with hst
  set S : Finset ℕ := Finset.range (prev + 1) with hS
  have hcard : st.U.card + S.card < st.B.card := by
    simpa [hk, hst, hS, Finset.card_range] using (chooseStage_spec F h prev)
  have hnot : st.val (chooseSafeBlock (st := st) (S := S) hcard) ∉ S :=
    chooseSafeBlock_val_not_mem (st := st) (S := S) hcard
  have hge : prev + 1 ≤ st.val (chooseSafeBlock (st := st) (S := S) hcard) := by
    by_contra hlt
    have : st.val (chooseSafeBlock (st := st) (S := S) hcard) < prev + 1 :=
      Nat.lt_of_not_ge hlt
    exact hnot (Finset.mem_range.2 this)
  have hlt : prev < st.val (chooseSafeBlock (st := st) (S := S) hcard) :=
    lt_of_lt_of_le (Nat.lt_succ_self prev) hge
  -- Unfold `blocks` at `n+1` and rewrite `blocks n` as `prev`.
  simpa [blocks, hprev, hk, hst, hS] using hlt

/--
As a consequence, `blocks` has unbounded range in the sense required by `KernelPackage.unbounded`.
-/
theorem unbounded_blocks (F : StageFamily) (h : HasSurplus F) :
    ∀ N (s : Finset ℕ), ∃ n ≥ N, blocks F h n ∉ s := by
  exact unbounded_of_strictMono_nat (blocks F h) (strictMono_blocks F h)

end StageFamily

end Erdos
