import Erdos.Basic
import Erdos.ShellStage

namespace Erdos

namespace ShellStage

open Erdos.Word

/--
If a shell stage has distinct block values on its allowed indices `B` (the `hinj` field), then the
finite word obtained by enumerating `B` and mapping `val` has no subperiod.

This packages the manuscript slogan “blocks are not ordinally simplifiable”.
-/
theorem not_hasSubPeriod_toList_map_val (st : Erdos.ShellStage) :
    ¬ Erdos.Word.HasSubPeriod (st.B.toList.map st.val) := by
  classical
  -- It suffices to show the mapped list is pairwise distinct.
  refine Erdos.Word.not_hasSubPeriod_of_pairwise_ne (w := st.B.toList.map st.val) ?_

  -- Auxiliary: on a nodup list whose elements all lie in `B`, mapping by an `InjOn` function
  -- yields a pairwise-distinct word.
  have pairwise_map_of_nodup_of_mem :
      ∀ (l : List ℕ),
        l.Nodup →
        (∀ x ∈ l, x ∈ st.B) →
        (l.map st.val).Pairwise (· ≠ ·) := by
    intro l hnodup hmem
    induction l with
    | nil =>
      simp
    | cons a tl ih =>
      have hcons := List.nodup_cons.1 hnodup
      have ha_not_mem : a ∉ tl := hcons.1
      have haB : a ∈ st.B := hmem a (by simp)
      have hmem_tl : ∀ x ∈ tl, x ∈ st.B := by
        intro x hx
        exact hmem x (by simp [hx])
      have hnodup_tl : tl.Nodup := hcons.2

      have hhead : ∀ b ∈ tl, st.val a ≠ st.val b := by
        intro b hbtl
        intro hEq
        have hbB : b ∈ st.B := hmem_tl b hbtl
        have hab : a = b := st.hinj haB hbB hEq
        exact ha_not_mem (by simpa [hab] using hbtl)

      have htail : (tl.map st.val).Pairwise (· ≠ ·) := ih hnodup_tl hmem_tl
      -- Build `Pairwise` for the mapped `cons` list.
      refine List.Pairwise.cons ?_ htail
      intro y hy
      rcases List.mem_map.1 hy with ⟨b, hb, rfl⟩
      exact hhead b hb

  -- Apply the auxiliary lemma to the finset enumeration list.
  refine pairwise_map_of_nodup_of_mem (l := st.B.toList) st.B.nodup_toList ?_
  intro x hx
  exact Finset.mem_toList.1 hx

end ShellStage

end Erdos
