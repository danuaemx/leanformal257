import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod

namespace Erdos

/-- The set of block indices `{1, …, μ}` used in the manuscript. -/
def blockIndices (μ : ℕ) : Finset ℕ :=
  (Finset.range (μ + 1)).filter (fun q => 1 ≤ q)

/-- The local carry-displacement “hazard predicate” for a term `n` at block index `q`. -/
def isHazard (L : ℕ) (M : ℕ → ℕ) (n q : ℕ) : Prop :=
  let r := (q * L) % n
  1 ≤ r ∧ r ≤ M n

instance decidablePred_isHazard (L : ℕ) (M : ℕ → ℕ) (n : ℕ) :
    DecidablePred (fun q : ℕ => isHazard L M n q) := by
  intro q
  unfold isHazard
  infer_instance

/--
A finitary approximation of the TeX map `Φ_{k,j}(q)`:

We treat the remainder `r = (q·L) mod n` as the candidate injection coordinate `z`.
A hazard token exists whenever this remainder lies in `[1, M(n)]`.

This is the minimal structure needed to define the hazard universe and the projection `Γ`.
-/
def phi (L : ℕ) (M : ℕ → ℕ) (active : Finset ℕ) (q : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {t | ∃ n ∈ active, t = (q, L, (q * L) % n) ∧ isHazard L M n q}

/--
The hazard universe `U_haz` as a finite set of tokens.

A token is represented by a pair `(n, q)` where:
- `n` is an active term in the current shell/layer, and
- `q` is a block index in `{1,…,μ}` satisfying the hazard predicate.

This matches the manuscript’s “disjoint union over n of H(n) tokens”, but uses an explicit
finite encoding.
-/
noncomputable def hazardTokens (μ L : ℕ) (M : ℕ → ℕ) (active : Finset ℕ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (active.product (blockIndices μ)).filter (fun t => isHazard L M t.1 t.2)

/-- The projection map `Γ : U_haz → B_total` sending a token to its corrupted block index. -/
def Gamma (t : ℕ × ℕ) : ℕ :=
  t.2

theorem Gamma_mem_blockIndices
    {μ L : ℕ} {M : ℕ → ℕ} {active : Finset ℕ}
    {t : ℕ × ℕ}
    (ht : t ∈ hazardTokens μ L M active) :
    Gamma t ∈ blockIndices μ := by
  -- `t ∈ filter` implies `t ∈ product`, hence its second component lies in `blockIndices`.
  classical
  have ht0 : t ∈ (active.product (blockIndices μ)).filter (fun t => isHazard L M t.1 t.2) := by
    simpa [hazardTokens] using ht
  have ht' : t ∈ active.product (blockIndices μ) := (Finset.mem_filter.1 ht0).1
  exact (Finset.mem_product.1 ht').2

end Erdos
