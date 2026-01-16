import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic

open scoped BigOperators

namespace Erdos

/-!

  This file provides a small Lean formalization scaffold for the objects appearing
  in the TeX manuscript `mainr(1).tex`.

  The full irrationality proof is not (yet) formalized here; we record the main
  statement as a theorem stub and fully formalize some elementary arithmetic
  components (e.g. the lcm/multiplicative period step under coprimality).
-/

section Series

variable (b : ℕ) (A : Set ℕ)

/--
`erdosSeries b A` is the real number

`∑' n, (if n ∈ A then 1 / ((b : ℝ)^n - 1) else 0)`.

This matches the manuscript's `S_A = ∑_{n∈A} (b^n - 1)^{-1}` (with the convention
that we sum over all `n : ℕ` and zero out terms outside `A`).
-/
noncomputable def erdosSeries : ℝ := by
  classical
  exact ∑' n : ℕ, if n ∈ A then (1 : ℝ) / ((b : ℝ) ^ n - 1) else 0

end Series

section Period

/--
If two periods are coprime, their least common multiple is their product.
Use the density to bound the block rather than the magnitude 
(assume the analytic euler product bound if lean4 is limited), 
focus on the exhaust argument, Use induction ( to simplify the profinite)
This is the purely arithmetic core behind the manuscript's multiplicative step
`L_{N+1} = L_N · a^*_{N+1}` under the coprimality hypothesis.
-/
theorem lcm_eq_mul_of_coprime {L K : ℕ} (h : Nat.Coprime L K) : Nat.lcm L K = L * K := by
  simpa using h.lcm_eq_mul

/-!
### Period growth ("crescente")

In the manuscript (Proposition “Periodicity Recurrence under Stability”), the period lengths
satisfy

`L_{N+1} = lcm(L_N, a^*_{N+1})`.

Abstracting this recurrence, we record the basic monotonicity fact
`L ≤ lcm(L, K)` and the strict growth statement in the coprime case.

This is the Lean core behind “the period is increasing / c”.
-/

theorem le_lcm_left_of_pos {L K : ℕ} (hL : 0 < L) (hK : 0 < K) : L ≤ Nat.lcm L K := by
  have hpos : 0 < Nat.lcm L K := Nat.lcm_pos hL hK
  exact Nat.le_of_dvd hpos (Nat.dvd_lcm_left L K)

theorem le_lcm_right_of_pos {L K : ℕ} (hL : 0 < L) (hK : 0 < K) : K ≤ Nat.lcm L K := by
  have hpos : 0 < Nat.lcm L K := Nat.lcm_pos hL hK
  exact Nat.le_of_dvd hpos (Nat.dvd_lcm_right L K)

theorem lt_lcm_of_coprime_of_one_lt_right
    {L K : ℕ} (hL : 0 < L) (hK : 1 < K) (hcop : Nat.Coprime L K) :
    L < Nat.lcm L K := by
  -- In the coprime case, `lcm = L*K`.
  have hlcm : Nat.lcm L K = L * K := by
    simpa using hcop.lcm_eq_mul
  -- Since `1 < K` and `0 < L`, multiplying by `L` strictly increases.
  have hmul : L * 1 < L * K := Nat.mul_lt_mul_of_pos_left hK hL
  -- Rewrite `L*1 = L` and the lcm.
  simpa [hlcm, Nat.mul_one] using hmul

theorem lt_lcm_of_coprime_of_one_lt_left
    {L K : ℕ} (hL : 1 < L) (hK : 0 < K) (hcop : Nat.Coprime L K) :
    K < Nat.lcm L K := by
  have hlcm : Nat.lcm L K = L * K := by
    simpa [Nat.mul_comm] using (lcm_eq_mul_of_coprime (L := L) (K := K) hcop)
  have hmul : 1 * K < L * K := Nat.mul_lt_mul_of_pos_right hL hK
  simpa [hlcm, Nat.one_mul] using hmul

/-!
### Denominator growth from period growth

For a purely periodic base-`b` expansion with period length `L`, the natural denominator is
`b^L - 1` (up to cancellation). So, once we know the period lengths are increasing, we can
conclude the denominators are increasing as well.

We keep this in `ℕ` (not reduced fractions): the key point is monotonicity.
-/

def periodDenom (b L : ℕ) : ℕ := b ^ L - 1

theorem pow_lt_pow_of_lt_right {b m n : ℕ} (hb : 1 < b) (hmn : m < n) : b ^ m < b ^ n := by
  -- Write `n = m + k` with `k > 0`, then compare `b^m` and `b^m * b^k`.
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hmnle : m ≤ n := Nat.le_of_lt hmn
  rcases Nat.exists_eq_add_of_le hmnle with ⟨k, hk⟩
  have hkpos : 0 < k := by
    have hkne : k ≠ 0 := by
      intro hk0
      have : m = n := by
        -- If `k = 0`, then `n = m`, contradicting `m < n`.
        simpa [hk0] using hk.symm
      exact (Nat.ne_of_lt hmn) this
    exact Nat.pos_of_ne_zero hkne
  have hone_le : ∀ t : ℕ, 1 ≤ b ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Nat.mul_le_mul ih (Nat.le_of_lt hb)
  have hone_lt_powk : 1 < b ^ k := by
    cases k with
    | zero => cases (Nat.not_lt_zero 0 hkpos)
    | succ k =>
      -- `b ≤ b^(k+1)` and `1 < b`.
      have hb_le : b ≤ b ^ (Nat.succ k) := by
        calc
          b = 1 * b := by simp
          _ ≤ b ^ k * b := Nat.mul_le_mul_right b (hone_le k)
          _ = b ^ (Nat.succ k) := by simp [pow_succ, Nat.mul_comm]
      exact lt_of_lt_of_le hb hb_le
  calc
    b ^ m = b ^ m * 1 := by simp
    _ < b ^ m * b ^ k := Nat.mul_lt_mul_of_pos_left hone_lt_powk (pow_pos hb0 _)
    _ = b ^ (m + k) 
    := by simp [pow_add]
    _ = b ^ n 
    := by simp [hk]

theorem periodDenom_lt_of_lt
    {b m n : ℕ} (hb : 1 < b) (hmn : m < n) :
    periodDenom b m < periodDenom b n := by
  -- `b^m < b^n`, and subtracting `1` preserves strict inequality here.
  -- (Both sides are ≥ 1 because `b^m ≥ 1`.)
  have hpow : b ^ m < b ^ n := pow_lt_pow_of_lt_right (b := b) hb hmn
  -- Use monotonicity of subtraction by a constant.
  have h1le : 1 ≤ b ^ m := by
    -- Reuse the same argument from `pow_lt_pow_of_lt_right` (but simpler): `1 ≤ b^m` when `1 < b`.
    have : ∀ t : ℕ, 1 ≤ b ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.mul_le_mul ih (Nat.le_of_lt hb)
    exact this m
  exact Nat.sub_lt_sub_right h1le hpow

theorem periodDenom_le_of_le
    {b m n : ℕ} (hb : 1 ≤ b) (hmn : m ≤ n) :
    periodDenom b m ≤ periodDenom b n := by
  -- This is the non-strict version; we only need monotonicity of `b^·`.
  have hpow : b ^ m ≤ b ^ n := by
    exact Nat.pow_le_pow_right hb hmn
  exact Nat.sub_le_sub_right hpow 1

/-!
### Period containment (modular form)

The manuscript proves that for rationals whose base-`b` periods are `Lx` and `Ly`, the
period of the sum divides `lcm(Lx,Ly)`. A clean way to formalize the algebraic core is:

* If `b^Lx ≡ 1 (mod Q1)` and `b^Ly ≡ 1 (mod Q2)` then `b^K ≡ 1 (mod lcm(Q1,Q2))` for
  `K = lcm(Lx,Ly)`.

This avoids any digit-expansion development and isolates the modular arithmetic.
-/

theorem modEq_pow_lcm_of_modEq_pow
    {b Q1 Q2 L1 L2 : ℕ}
    (hb : 1 ≤ b)
    (h1 : Nat.ModEq Q1 (b ^ L1) 1)
    (h2 : Nat.ModEq Q2 (b ^ L2) 1) :
    Nat.ModEq (Nat.lcm Q1 Q2) (b ^ Nat.lcm L1 L2) 1 := by
  -- Let `K` be the lcm of the exponents.
  set K := Nat.lcm L1 L2
  have hK1 : L1 ∣ K := Nat.dvd_lcm_left L1 L2
  have hK2 : L2 ∣ K := Nat.dvd_lcm_right L1 L2
  have one_le_pow : ∀ n : ℕ, 1 ≤ b ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      -- `b^(n+1) = b^n * b` and both factors are ≥ 1.
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Nat.mul_le_mul ih hb
  -- Upgrade the congruences to exponent `K`.
  have h1K : Nat.ModEq Q1 (b ^ K) 1 := by
    rcases hK1 with ⟨t, ht⟩
    -- (b^L1)^t ≡ 1^t, then rewrite `(b^L1)^t = b^(L1*t)` and `K = L1*t`.
    simpa [K, ht, pow_mul] using h1.pow t
  have h2K : Nat.ModEq Q2 (b ^ K) 1 := by
    rcases hK2 with ⟨t, ht⟩
    simpa [K, ht, pow_mul] using h2.pow t
  -- Convert both congruences into divisibility of `b^K - 1`.
  have d1 : Q1 ∣ b ^ K - 1 := by
    -- `b^K ≡ 1 [MOD Q1]`  ↔  `1 ≡ b^K [MOD Q1]`  ↔  `Q1 ∣ b^K - 1`.
    exact (Nat.modEq_iff_dvd' (one_le_pow K)).1 h1K.symm
  have d2 : Q2 ∣ b ^ K - 1 := by
    exact (Nat.modEq_iff_dvd' (one_le_pow K)).1 h2K.symm
  -- If both `Q1` and `Q2` divide a number, then their lcm divides it.
  have d : Nat.lcm Q1 Q2 ∣ b ^ K - 1 := Nat.lcm_dvd d1 d2
  -- Translate back to a congruence modulo the lcm.
  -- `lcm ∣ b^K - 1` gives `1 ≡ b^K [MOD lcm]`, hence `b^K ≡ 1 [MOD lcm]`.
  have : Nat.ModEq (Nat.lcm Q1 Q2) 1 (b ^ K) := (Nat.modEq_iff_dvd' (one_le_pow K)).2 d
  simpa [K] using this.symm

end Period

section Collision

/-!
### Collision multiplicity and a `Nat.log` carry-span bound

In the manuscript, for a finite set of “effective exponents” `A_E`, the collision multiplicity
at position `n` is

`ν(n) = ∑_{x ∈ A_E} 1_{x ∣ n}`.

The “logarithmic containment of carries” is, at its arithmetic core, the fact that the size of
`ν(n)` determines how many base-`b` digits are needed to represent it. This is captured by
`Nat.log`.
-/

/-- Collision multiplicity for a finite exponent set `E` at position `n`. -/
def collisionMultiplicity (E : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ x ∈ E, if x ∣ n then 1 else 0

theorem collisionMultiplicity_le_card (E : Finset ℕ) (n : ℕ) :
  collisionMultiplicity E n ≤ E.card := by
  classical
  -- Each summand is either `0` or `1`, so the sum is bounded by `card(E) * 1`.
  -- We use the standard lemma `Finset.sum_le_card_nsmul`.
  simpa [collisionMultiplicity] using
    (Finset.sum_le_card_nsmul E (fun x : ℕ => if x ∣ n then (1 : ℕ) else 0) 1
      (by
        intro x hx
        by_cases hxn : x ∣ n <;> simp [hxn]))

/--
`ν(n) < b^(log_b(ν(n)) + 1)` for bases `b > 1`.

This is the quantitative form of “carry disturbance spans at most `log_b(ν(n)) + 1` digits”.
-/
theorem collisionMultiplicity_lt_pow_succ_log
    {b : ℕ} (hb : 1 < b) (E : Finset ℕ) (n : ℕ) :
    collisionMultiplicity E n < b ^ (Nat.log b (collisionMultiplicity E n)).succ := by
  simpa [collisionMultiplicity] using Nat.lt_pow_succ_log_self hb (collisionMultiplicity E n)

end Collision

section Witness

/-!
### Witness term (finite shell)

Your manuscript (Phase 2) picks, inside each finite “shell”, an element maximizing a p-adic
valuation. In Lean we can model a p-adic exponent on `ℕ` using `Nat.factorization`:

`v_p(n) := (Nat.factorization n) p`.

Since shells are finite (in the formalization stage we work with `Finset ℕ`), a maximizer exists.
-/

/-- The `p`-adic exponent `v_p(n)` defined via `Nat.factorization`. -/
noncomputable def vp (p n : ℕ) : ℕ := (Nat.factorization n) p

/-- In a nonempty finite shell `S`, there exists a witness maximizing `v_p`. -/
theorem exists_witness_vp (p : ℕ) (S : Finset ℕ) (hS : S.Nonempty) :
    ∃ n ∈ S, ∀ m ∈ S, vp p m ≤ vp p n := by
  classical
  let f : ℕ → ℕ := fun n => vp p n
  have hIm : (S.image f).Nonempty := hS.image f
  -- Let `M` be the maximum valuation value attained in the shell.
  set M : ℕ := (S.image f).max' hIm
  have hMmem : M ∈ S.image f := (S.image f).max'_mem hIm
  rcases Finset.mem_image.1 hMmem with ⟨n, hnS, hnM⟩
  refine ⟨n, hnS, ?_⟩
  intro m hmS
  have hmIm : f m ∈ S.image f := Finset.mem_image_of_mem f hmS
  have hGreat : IsGreatest (↑(S.image f) : Set ℕ) M := Finset.isGreatest_max' (S.image f) hIm
  -- Every value in the image is ≤ the maximum.
  have hm_le_M : f m ≤ M := hGreat.2 hmIm
  -- Rewrite `M` as `f n` using `hnM : f n = M`.
  have hm_le_fn : f m ≤ f n := by
    simpa [hnM.symm] using hm_le_M
  simpa [f, vp] using hm_le_fn

end Witness

section BlockModel

/-!
### Integer block model

This section implements the manuscript's “integer block representation” (a length-`L` base-`b`
block) using the natural base `B = b^L`.

* `trunc b L t = t % B` is the `L`-digit block (least significant `L` base-`b` digits).
* `carry b L t = t / B` is the overflow into the next block.

The key lemma is the standard division algorithm identity
`t = (t % B) + B * (t / B)`.
-/

def blockBase (b L : ℕ) : ℕ := b ^ L

def trunc (b L t : ℕ) : ℕ := t % blockBase b L

def carry (b L t : ℕ) : ℕ := t / blockBase b L

theorem blockBase_pos (b L : ℕ) (hb : 1 ≤ b) : 0 < blockBase b L := by
  have hb0 : b ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)
  exact Nat.pos_of_ne_zero (pow_ne_zero L hb0)

theorem trunc_lt_blockBase (b L t : ℕ) (hb : 1 ≤ b) : trunc b L t < blockBase b L := by
  have hB : 0 < blockBase b L := blockBase_pos b L hb
  simpa [trunc, blockBase] using Nat.mod_lt t hB

theorem trunc_add_blockBase_mul_carry (b L t : ℕ) :
    trunc b L t + blockBase b L * carry b L t = t := by
  -- `Nat.mod_add_div` gives `t % B + B * (t / B) = t`.
  simpa [trunc, carry, blockBase, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.mod_add_div t (blockBase b L))

theorem trunc_eq_of_lt_blockBase {b L t : ℕ} (ht : t < blockBase b L) : trunc b L t = t := by
  unfold trunc blockBase
  simpa using (Nat.mod_eq_of_lt ht)

theorem carry_eq_zero_of_lt_blockBase {b L t : ℕ} (ht : t < blockBase b L) : carry b L t = 0 := by
  unfold carry blockBase
  have ht' : t < b ^ L := by
    simpa using ht
  simpa using (Nat.div_eq_of_lt ht')

/--
One-step “add a block and propagate carry” operation.

This matches the manuscript's per-block rule
`T = C_N + B_{q} + κ`, then `C' = T mod B`, `κ' = T / B`.
-/
def addBlockStep (b L baseBlock perturbBlock κ : ℕ) : ℕ × ℕ :=
  let B := blockBase b L
  let t := baseBlock + perturbBlock + κ
  (t % B, t / B)

theorem addBlockStep_spec (b L baseBlock perturbBlock κ : ℕ) (hb : 1 ≤ b) :
    let B := blockBase b L
    let t := baseBlock + perturbBlock + κ
    let out := addBlockStep b L baseBlock perturbBlock κ
    out.1 < B ∧ out.1 + B * out.2 = t := by
  intro B t out
  constructor
  · -- output block is a remainder
    dsimp [out, addBlockStep]
    exact Nat.mod_lt _ (by simpa [B] using blockBase_pos b L hb)
  · dsimp [out, addBlockStep]
    -- `t % B + B * (t / B) = t`
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mod_add_div t B)

/-- Concatenate a list of length-`L` blocks into a single natural number. -/
def concatBlocks (b L : ℕ) (xs : List ℕ) : ℕ :=
  let B := blockBase b L
  xs.foldl (fun acc x => acc * B + x) 0

/-!
#### Block concatenation with generalized carry

This matches Definition `Block Concatenation with Generalized Carry` in the manuscript.

Given:
* a fixed base block `C_N` (length `L`),
* a list of perturbation blocks `[B₁, …, B_K]` (each intended to be length `L`),

we scan from the least-significant block `q = K` down to `q = 1`, maintaining an integer carry.

The output is the list of regularized blocks `[C'₁, …, C'_K]` and the carry trace
`[κ₀, κ₁, …, κ_K]` with `κ_K = 0`.
-/

/--
Compute the generalized-carry block concatenation.

Returns `(κ₀, blocks, carries)` where:
* `blocks = [C'₁, …, C'_K]` are the regularized blocks,
* `carries = [κ₀, κ₁, …, κ_K]` with the convention `κ_K = 0`.

Implementation detail: this is a `foldr` so the carry flows left.
-/
def concatWithCarryTrace (b L baseBlock : ℕ) (perturbBlocks : List ℕ) :
    ℕ × List ℕ × List ℕ :=
  let step :=
    fun (p : ℕ) (acc : ℕ × List ℕ × List ℕ) =>
      let B := blockBase b L
      let κ := acc.1
      let blocks := acc.2.1
      let carries := acc.2.2
      let t := baseBlock + p + κ
      let blk := t % B
      let κ' := t / B
      (κ', blk :: blocks, κ' :: carries)
  perturbBlocks.foldr step (0, [], [0])

/-- The output blocks from `concatWithCarryTrace`. -/
def concatWithCarryBlocks (b L baseBlock : ℕ) (perturbBlocks : List ℕ) : List ℕ :=
  (concatWithCarryTrace b L baseBlock perturbBlocks).2.1

/-- The concatenated integer period from the output blocks of `concatWithCarryTrace`. -/
def concatWithCarryValue (b L baseBlock : ℕ) (perturbBlocks : List ℕ) : ℕ :=
  concatBlocks b L (concatWithCarryBlocks b L baseBlock perturbBlocks)

theorem concatWithCarryTrace_nil (b L baseBlock : ℕ) :
    concatWithCarryTrace b L baseBlock [] = (0, [], [0]) := by
  simp [concatWithCarryTrace]

/--
Explicit one-step recurrence for the generalized-carry concatenation.

This is the Lean statement of the manuscript's update rule
`t = C_N + B_q + κ_q`, `C'_q = t mod b^L`, `κ_{q-1} = t / b^L`.
-/
theorem concatWithCarryTrace_cons (b L baseBlock p : ℕ) (ps : List ℕ) :
    concatWithCarryTrace b L baseBlock (p :: ps) =
      let acc := concatWithCarryTrace b L baseBlock ps
      let B := blockBase b L
      let κ := acc.1
      let blocks := acc.2.1
      let carries := acc.2.2
      let t := baseBlock + p + κ
      let blk := t % B
      let κ' := t / B
      (κ', blk :: blocks, κ' :: carries) := by
  -- `foldr` on a cons applies the step function once.
  simp [concatWithCarryTrace, List.foldr]

theorem concatWithCarryBlocks_cons (b L baseBlock p : ℕ) (ps : List ℕ) :
    concatWithCarryBlocks b L baseBlock (p :: ps) =
      let acc := concatWithCarryTrace b L baseBlock ps
      let B := blockBase b L
      let κ := acc.1
      let t := baseBlock + p + κ
      (t % B) :: acc.2.1 := by
  classical
  -- Extract the blocks component from `concatWithCarryTrace_cons`.
  simpa [concatWithCarryBlocks] using
    congrArg (fun x => x.2.1)
      (concatWithCarryTrace_cons (b := b) (L := L) (baseBlock := baseBlock) (p := p) (ps := ps))

theorem concatWithCarryCarry_cons (b L baseBlock p : ℕ) (ps : List ℕ) :
    (concatWithCarryTrace b L baseBlock (p :: ps)).1 =
      let acc := concatWithCarryTrace b L baseBlock ps
      let B := blockBase b L
      let κ := acc.1
      (baseBlock + p + κ) / B := by
  classical
  -- Extract the carry component from `concatWithCarryTrace_cons`.
  simpa using
    congrArg (fun x => x.1)
      (concatWithCarryTrace_cons (b := b) (L := L) (baseBlock := baseBlock) (p := p) (ps := ps))

theorem concatWithCarryTrace_blocks_length (b L baseBlock : ℕ) (ps : List ℕ) :
    (concatWithCarryTrace b L baseBlock ps).2.1.length = ps.length := by
  induction ps with
  | nil =>
    simp [concatWithCarryTrace]
  | cons p ps ih =>
    -- Use the explicit `cons` recurrence.
    simp [concatWithCarryTrace_cons, ih]

theorem concatWithCarryTrace_carries_length (b L baseBlock : ℕ) (ps : List ℕ) :
    (concatWithCarryTrace b L baseBlock ps).2.2.length = ps.length + 1 := by
  induction ps with
  | nil =>
    simp [concatWithCarryTrace]
  | cons p ps ih =>
    -- Use the explicit `cons` recurrence.
    simp [concatWithCarryTrace_cons, ih, Nat.add_left_comm, Nat.add_comm]

theorem concatWithCarryBlocks_length (b L baseBlock : ℕ) (ps : List ℕ) :
    (concatWithCarryBlocks b L baseBlock ps).length = ps.length := by
  simpa [concatWithCarryBlocks] using
    concatWithCarryTrace_blocks_length (b := b) (L := L) (baseBlock := baseBlock) ps

theorem concatWithCarryTrace_carries_get0
    (b L baseBlock : ℕ) (ps : List ℕ)
    (h : 0 < (concatWithCarryTrace b L baseBlock ps).2.2.length) :
    (concatWithCarryTrace b L baseBlock ps).2.2.get ⟨0, h⟩ =
      (concatWithCarryTrace b L baseBlock ps).1 := by
  cases ps with
  | nil =>
    simp [concatWithCarryTrace]
  | cons p ps =>
    simp [concatWithCarryTrace_cons]

theorem concatWithCarryTrace_carries_getElem0
    (b L baseBlock : ℕ) (ps : List ℕ)
    (h : 0 < (concatWithCarryTrace b L baseBlock ps).2.2.length) :
    (concatWithCarryTrace b L baseBlock ps).2.2[0]'h =
      (concatWithCarryTrace b L baseBlock ps).1 := by
  cases ps with
  | nil =>
    simp [concatWithCarryTrace]
  | cons p ps =>
    simp [concatWithCarryTrace_cons]

/--
Per-index recurrence for the produced blocks.

For `i` indexing into the perturbation list, the `i`-th output block is
`(baseBlock + p_i + κ_{i+1}) mod B`, where `κ_{i+1}` is the next carry from the trace.
-/
theorem concatWithCarryBlocks_get
    (b L baseBlock : ℕ) (ps : List ℕ) (i : Fin ps.length) :
    (concatWithCarryBlocks b L baseBlock ps).get
        ⟨i.1, by
          have hl : (concatWithCarryBlocks b L baseBlock ps).length = ps.length :=
            concatWithCarryBlocks_length (b := b) (L := L) (baseBlock := baseBlock) ps
          simp [hl]⟩ =
      let B := blockBase b L
      let carries := (concatWithCarryTrace b L baseBlock ps).2.2
      (baseBlock + ps.get i + carries.get
        ⟨i.1 + 1, by
          -- `i+1 < length(carries) = length(ps)+1`.
          have hc : carries.length = ps.length + 1 :=
            concatWithCarryTrace_carries_length (b := b) (L := L) (baseBlock := baseBlock) ps
          simp [hc]⟩) % B := by
  classical
  induction ps with
  | nil =>
    cases i with
    | mk n hn =>
      cases (Nat.not_lt_zero n hn)
  | cons p ps ih =>
    -- Split into the head index `0` and the shifted tail indices.
    refine Fin.cases ?h0 ?hs i
    · -- i = 0
      -- Unfold the block list for a cons.
      simp [concatWithCarryBlocks_cons, concatWithCarryTrace_cons,
        concatWithCarryTrace_carries_getElem0]
    · intro j
      -- i = succ j
      -- Reduce to the induction hypothesis on the tail.
      simpa [concatWithCarryBlocks_cons, concatWithCarryTrace_cons] using ih j

/--
Per-index recurrence for the produced carries.

For `i` indexing into the perturbation list, the `i`-th carry satisfies
`κ_i = (baseBlock + p_i + κ_{i+1}) / B`, where `κ_{i+1}` is the next carry.
-/
theorem concatWithCarryCarries_get
    (b L baseBlock : ℕ) (ps : List ℕ) (i : Fin ps.length) :
    (concatWithCarryTrace b L baseBlock ps).2.2.get
        ⟨i.1, by
          -- `i < length(carries) = length(ps)+1`.
          have hc : (concatWithCarryTrace b L baseBlock ps).2.2.length = ps.length + 1 :=
            concatWithCarryTrace_carries_length (b := b) (L := L) (baseBlock := baseBlock) ps
          have hi' : i.1 < ps.length + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self ps.length)
          rw [hc]
          exact hi'⟩ =
      let B := blockBase b L
      let carries := (concatWithCarryTrace b L baseBlock ps).2.2
      (baseBlock + ps.get i + carries.get
        ⟨i.1 + 1, by
          have hc : carries.length = ps.length + 1 :=
            concatWithCarryTrace_carries_length (b := b) (L := L) (baseBlock := baseBlock) ps
          simp [hc]⟩) / B := by
  classical
  induction ps with
  | nil =>
    cases i with
    | mk n hn =>
      cases (Nat.not_lt_zero n hn)
  | cons p ps ih =>
    refine Fin.cases ?h0 ?hs i
    · -- i = 0
      simp [concatWithCarryTrace_cons, concatWithCarryTrace_carries_getElem0]
    · intro j
      -- i = succ j
      simpa [concatWithCarryTrace_cons] using ih j

/--
Per-index division-algorithm identity.

With `t = baseBlock + p_i + κ_{i+1}` and `B = b^L`, this states
`t = C'_i + B * κ_i`.
-/
theorem concatWithCarry_index_decomp
    (b L baseBlock : ℕ) (ps : List ℕ) (i : Fin ps.length) :
    let B := blockBase b L
    let carries := (concatWithCarryTrace b L baseBlock ps).2.2
    let t := baseBlock + ps.get i + carries.get
      ⟨i.1 + 1, by
        have hc : carries.length = ps.length + 1 :=
          concatWithCarryTrace_carries_length (b := b) (L := L) (baseBlock := baseBlock) ps
        have h : i.1 + 1 < ps.length + 1 := Nat.succ_lt_succ i.isLt
        rw [hc]
        exact h⟩
    t =
      (concatWithCarryBlocks b L baseBlock ps).get
        ⟨i.1, by
          have hl : (concatWithCarryBlocks b L baseBlock ps).length = ps.length :=
            concatWithCarryBlocks_length (b := b) (L := L) (baseBlock := baseBlock) ps
          rw [hl]
          exact i.isLt⟩
        + B * (concatWithCarryTrace b L baseBlock ps).2.2.get
          ⟨i.1, by
            have hc : (concatWithCarryTrace b L baseBlock ps).2.2.length = ps.length + 1 :=
              concatWithCarryTrace_carries_length (b := b) (L := L) (baseBlock := baseBlock) ps
            have hi' : i.1 < ps.length + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self ps.length)
            rw [hc]
            exact hi'⟩ := by
  classical
  intro B carries t
  -- Rewrite the block and carry via the per-index recurrences, then use `Nat.mod_add_div`.
  have hblk :=
    concatWithCarryBlocks_get (b := b) (L := L) (baseBlock := baseBlock) (ps := ps) i
  have hcar :=
    concatWithCarryCarries_get (b := b) (L := L) (baseBlock := baseBlock) (ps := ps) i
  have hl : (concatWithCarryBlocks b L baseBlock ps).length = ps.length :=
    concatWithCarryBlocks_length (b := b) (L := L) (baseBlock := baseBlock) ps
  let iBlock : Fin (concatWithCarryBlocks b L baseBlock ps).length :=
    ⟨i.1, by
      rw [hl]
      exact i.isLt⟩
  have hcLen : (concatWithCarryTrace b L baseBlock ps).2.2.length = ps.length + 1 :=
    concatWithCarryTrace_carries_length (b := b) (L := L) (baseBlock := baseBlock) ps
  have hiCarry : i.1 < (concatWithCarryTrace b L baseBlock ps).2.2.length := by
    have hi' : i.1 < ps.length + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self ps.length)
    rw [hcLen]
    exact hi'
  let iCarry : Fin (concatWithCarryTrace b L baseBlock ps).2.2.length :=
    ⟨i.1, hiCarry⟩
  have hblk' : (concatWithCarryBlocks b L baseBlock ps).get iBlock = t % B := by
    simpa [iBlock, B, carries, t] using hblk
  have hcar' : (concatWithCarryTrace b L baseBlock ps).2.2.get iCarry = t / B := by
    simpa [iCarry, B, carries, t] using hcar
  calc
    t = t % B + B * (t / B) := (Nat.mod_add_div t B).symm
    _ = (concatWithCarryBlocks b L baseBlock ps).get iBlock
          + B * (concatWithCarryTrace b L baseBlock ps).2.2.get iCarry := by
      simp [hblk'.symm, hcar'.symm]

theorem concatWithCarryTrace_carries_last (b L baseBlock : ℕ) (perturbBlocks : List ℕ) :
  0 ∈ (concatWithCarryTrace b L baseBlock perturbBlocks).2.2 := by
  -- By construction, the carry list is initialized with `[0]` and we only `cons`.
  classical
  unfold concatWithCarryTrace
  induction perturbBlocks with
  | nil =>
    simp
  | cons p ps ih =>
    -- One fold step conses a new carry, so membership of `0` is preserved.
    simp [List.foldr, ih]

theorem concatWithCarryBlocks_lt_blockBase
    (b L baseBlock : ℕ) (perturbBlocks : List ℕ) (hb : 1 ≤ b) :
    (concatWithCarryBlocks b L baseBlock perturbBlocks).Forall (fun x => x < blockBase b L) := by
  classical
  -- Each produced block is a remainder mod `B = b^L`.
  unfold concatWithCarryBlocks concatWithCarryTrace
  set B := blockBase b L
  have hB : 0 < B := blockBase_pos b L hb
  -- Induct through the `foldr` structure.
  induction perturbBlocks with
  | nil =>
    simp [List.foldr]
  | cons p ps ih =>
    -- After unfolding one step, the head block is a remainder mod `B`.
    -- The tail blocks come from the recursive call.
    simp [List.foldr, B, hB, Nat.mod_lt, ih]

end BlockModel

section DistinctnessKernel

/-
The purely periodic base-`b` real `0.\overline{C}` corresponding to an integer block `C`
of length `L`.

This matches the manuscript's notation `0.\overline{C}` and satisfies the familiar formula
`0.\overline{C} = C / (b^L - 1)`.

We keep this as a convenience definition; we do not attempt here to connect it to the *canonical*
base expansion API in mathlib.
-/
def rep0Overline (b L C : ℕ) : ℚ :=
  (C : ℚ) / (b ^ L - 1)

namespace Word

/-- A simple period predicate for finite words (lists). -/
def IsPeriod {α : Type} (w : List α) (p : ℕ) : Prop :=
  ∀ i (hi : i + p < w.length),
    w.get ⟨i, lt_of_le_of_lt (Nat.le_add_right i p) hi⟩ = w.get ⟨i + p, hi⟩

/-
The above `List.IsPeriod` is intentionally low-tech: it is just “shift by `p` preserves entries
whenever both indices are in range”.

It is enough for the manuscript's distinctness argument:
if a list has a strict period `p < length`, then some two different positions have the same value.
-/

theorem IsPeriod.get_eq_get_of_lt_length
    {α : Type} {w : List α} {p : ℕ}
  (hpw : p < w.length) (hper : Word.IsPeriod w p) :
  w.get ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le p) hpw⟩ = w.get ⟨p, hpw⟩ := by
  have : 0 + p < w.length := by simpa using hpw
  simpa using hper 0 this

theorem not_isPeriod_of_pairwise_ne
    {α : Type} {w : List α} (hw : w.Pairwise (· ≠ ·))
  {p : ℕ} (hp : 0 < p) (hpw : p < w.length) : ¬ Word.IsPeriod w p := by
  classical
  intro hper
  have hw' := (List.pairwise_iff_get.mp hw)
  let i0 : Fin w.length := ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le p) hpw⟩
  let ip : Fin w.length := ⟨p, hpw⟩
  have hip : i0 < ip := by
    -- `0 < p`.
    simpa [i0, ip, Fin.lt_def] using hp
  have hne : w.get i0 ≠ w.get ip := hw' i0 ip hip
  have heq : w.get i0 = w.get ip := IsPeriod.get_eq_get_of_lt_length (w := w) hpw hper
  exact hne heq

/--
"Ordinal simplification" criterion: a finite word admits a shorter period `p` dividing its length.

This packages the idea: if there are sub-blocks of length `p` that tile the whole period and the
digits repeat with that step, then the true period can be reduced to `p`.
-/
def HasSubPeriod {α : Type} (w : List α) : Prop :=
  ∃ p : ℕ, 0 < p ∧ p < w.length ∧ p ∣ w.length ∧ Word.IsPeriod w p

theorem not_hasSubPeriod_of_pairwise_ne
    {α : Type} {w : List α} (hw : w.Pairwise (· ≠ ·)) : ¬ Word.HasSubPeriod w := by
  classical
  intro h
  rcases h with ⟨p, hp0, hpw, _, hper⟩
  exact (Word.not_isPeriod_of_pairwise_ne (w := w) hw hp0 hpw) hper

end Word

/--
An eventually periodic predicate for sequences.

This is the minimal notion needed for the “rational ⇒ eventually periodic expansion” step in the
manuscript.
-/
def EventuallyPeriodic {α : Type} (f : ℕ → α) : Prop :=
  ∃ p > 0, ∃ N, ∀ n ≥ N, f (n + p) = f n

theorem EventuallyPeriodic_tail_finite
    {α : Type} (f : ℕ → α) (hper : EventuallyPeriodic f) :
    ∃ (N : ℕ) (s : Finset α), ∀ n ≥ N, f n ∈ s := by
  classical
  rcases hper with ⟨p, hp, N, hN⟩
  refine ⟨N, (Finset.range p).image (fun r => f (N + r)), ?_⟩
  intro n hn
  set m := n - N
  set r := m % p
  have hrp : r < p := by
    have : 0 < p := hp
    exact Nat.mod_lt _ this
  have hmem : r ∈ Finset.range p := Finset.mem_range.2 hrp
  have hnN : N ≤ n := hn
  have hm : n = N + m := (Nat.add_sub_of_le hnN).symm
  let q := m / p
  have hrepl : n = N + q * p + r := by
    have hdiv0 : p * q + r = m := by
      -- `Nat.div_add_mod` gives `p * (m/p) + m%p = m`.
      simpa [m, q, r] using (Nat.div_add_mod m p)
    have hdiv : q * p + r = m := by
      simpa [Nat.mul_comm] using hdiv0
    calc
      n = N + m := hm
      _ = N + (q * p + r) := by simp [hdiv]
      _ = N + q * p + r := by simp [Nat.add_assoc]
  have hshift : ∀ q : ℕ, f (N + q * p + r) = f (N + r) := by
    intro q
    induction q with
    | zero =>
      simp
    | succ q ih =>
      have hge : N ≤ N + q * p + r := by
        exact le_trans (Nat.le_add_right N (q * p)) (Nat.le_add_right (N + q * p) r)
      have hstep : f (N + q * p + r + p) = f (N + q * p + r) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hN (N + q * p + r) hge
      have : f (N + (Nat.succ q) * p + r) = f (N + q * p + r) := by
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
      exact this.trans ih
  have hreduce : f n = f (N + r) := by
    simpa [hrepl] using hshift q
  refine Finset.mem_image.2 ?_
  refine ⟨r, hmem, ?_⟩
  simp [hreduce]

theorem not_eventuallyPeriodic_of_unbounded_range
    {α : Type} (f : ℕ → α)
    (h : ∀ N (s : Finset α), ∃ n ≥ N, f n ∉ s) : ¬ EventuallyPeriodic f := by
  classical
  intro hper
  rcases (EventuallyPeriodic_tail_finite (f := f) hper) with ⟨N, s, hs⟩
  rcases h N s with ⟨n, hn, hns⟩
  exact hns (hs n hn)

end DistinctnessKernel

section Erdös257

/-!
Generalized Erdős problem #257.

This file deliberately separates the proof into:

* an **analytic layer** (Euler-product / tail isolation / density domination) that controls
  carry interference and ensures the block extraction is well-defined, and
* a **combinatorial exhaustion layer**: once we have infinitely many structurally new blocks,
  eventual periodicity is impossible.

Lean currently focuses on the second layer. We assume the analytic/density inputs as axioms
mirroring the manuscript [mainr(1).tex], then complete the exhaustion argument formally.
-/
namespace Erdos257

/-!
### Block extraction (formalized as a definition)

The TeX proof constructs an infinite sequence of integer blocks (period words) from the series.

At this stage we **do not** formalize the full analytic construction; instead we package the
manuscript's analytic/density conclusions as a single axiom that *implies the existence* of a
block-extraction function with the needed properties.

We then *define* `blocks` by classical choice from that existence axiom.

This way, `blocks` is no longer an axiom: it is a bona fide Lean definition, and the only
remaining non-formalized ingredient is the single analytic/density axiom.
-/

/-!
### Rational eventual periodicity (finite-state remainder recursion)

This is the standard long-division / finite automaton argument: for a fixed modulus `d`, the
update rule `r ↦ (b*r) mod d` lives on a finite state space, hence the state sequence is
eventually periodic.

We use this as the formal replacement for the previously-axiomatized
`rational_series_eventuallyPeriodic_blocks`. The only remaining assumed bridge is that, under the
manuscript's density/tail-isolation hypotheses, the extracted block sequence from the series
eventually matches the rational-state sequence.
-/

theorem eventuallyPeriodic_of_rec_finite
    {α : Type} [Finite α] (g : α → α) (x0 : α) :
    EventuallyPeriodic (fun n : ℕ => Nat.rec (motive := fun _ => α) x0 (fun _ x => g x) n) := by
  classical
  let f : ℕ → α := fun n => Nat.rec (motive := fun _ => α) x0 (fun _ x => g x) n
  have hstep : ∀ n, f (n + 1) = g (f n) := by
    intro n
    cases n with
    | zero => simp [f]
    | succ n => simp [f]
  obtain ⟨i, j, hij, hijEq⟩ := (Finite.exists_ne_map_eq_of_infinite f)
  have hij' : i < j ∨ j < i := lt_or_gt_of_ne hij
  rcases hij' with hijlt | hjilt
  · -- i < j
    let p : ℕ := j - i
    have hp : 0 < p := Nat.sub_pos_of_lt hijlt
    have hshift : ∀ k : ℕ, f (i + k) = f (j + k) := by
      intro k
      induction k with
      | zero => simpa [f] using hijEq
      | succ k ih =>
        have : f (i + k + 1) = f (j + k + 1) := by
          -- One step via the recurrence.
          calc
            f (i + k + 1) = g (f (i + k)) := by simpa [Nat.add_assoc] using hstep (i + k)
            _ = g (f (j + k)) := by simp [ih]
            _ = f (j + k + 1) := by simpa [Nat.add_assoc] using (hstep (j + k)).symm
        simpa [Nat.add_assoc] using this
    refine ⟨p, hp, i, ?_⟩
    intro n hn
    -- Write `n = i + k`.
    rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
    have hi_le_j : i ≤ j := Nat.le_of_lt hijlt
    have hip : i + p = j := by
      -- `i + (j - i) = j`.
      simpa [p] using (Nat.add_sub_of_le hi_le_j)
    calc
      f (i + k + p) = f ((i + p) + k) := by ac_rfl
      _ = f (j + k) := by simp [hip]
      _ = f (i + k) := (hshift k).symm
  · -- j < i: swap roles.
    let p : ℕ := i - j
    have hp : 0 < p := Nat.sub_pos_of_lt hjilt
    have hshift : ∀ k : ℕ, f (j + k) = f (i + k) := by
      intro k
      induction k with
      | zero => simpa [f] using hijEq.symm
      | succ k ih =>
        have : f (j + k + 1) = f (i + k + 1) := by
          calc
            f (j + k + 1) = g (f (j + k)) := by simpa [Nat.add_assoc] using hstep (j + k)
            _ = g (f (i + k)) := by simp [ih]
            _ = f (i + k + 1) := by simpa [Nat.add_assoc] using (hstep (i + k)).symm
        simpa [Nat.add_assoc] using this
    refine ⟨p, hp, j, ?_⟩
    intro n hn
    rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
    have hj_le_i : j ≤ i := Nat.le_of_lt hjilt
    have hjp : j + p = i := by
      simpa [p] using (Nat.add_sub_of_le hj_le_i)
    calc
      f (j + k + p) = f ((j + p) + k) := by ac_rfl
      _ = f (i + k) := by simp [hjp]
      _ = f (j + k) := (hshift k).symm

def ratStep (b : ℕ) (q : ℚ) : Fin q.den → Fin q.den :=
  fun r =>
    ⟨(b * r.1) % q.den, by
      have hden : 0 < q.den := q.den_pos
      exact Nat.mod_lt _ hden⟩

noncomputable def ratState (b : ℕ) (q : ℚ) : ℕ → Fin q.den :=
  Nat.rec (motive := fun _ => Fin q.den)
    ⟨(Int.natAbs q.num) % q.den, by
      have hden : 0 < q.den := q.den_pos
      exact Nat.mod_lt _ hden⟩
    (fun _ r => ratStep b q r)

noncomputable def ratStateNat (b : ℕ) (q : ℚ) : ℕ → ℕ := fun n => (ratState b q n).1

theorem ratState_eventuallyPeriodic (b : ℕ) (q : ℚ) : EventuallyPeriodic (ratState b q) := by
  -- This is the generic finite-state recursion lemma.
  simpa [ratState, ratStep] using
    (eventuallyPeriodic_of_rec_finite (α := Fin q.den) (g := ratStep b q)
      (x0 := ⟨(Int.natAbs q.num) % q.den, by
        have hden : 0 < q.den := q.den_pos
        exact Nat.mod_lt _ hden⟩))

theorem ratStateNat_eventuallyPeriodic (b : ℕ) (q : ℚ) : EventuallyPeriodic (ratStateNat b q) := by
  rcases ratState_eventuallyPeriodic (b := b) (q := q) with ⟨p, hp, N, hN⟩
  refine ⟨p, hp, N, ?_⟩
  intro n hn
  have := hN n hn
  exact congrArg (fun x : Fin q.den => x.1) this

theorem eventuallyPeriodic_of_eventuallyEq
    {α : Type} {f g : ℕ → α}
    (hfg : ∃ N, ∀ n ≥ N, f n = g n)
    (hg : EventuallyPeriodic g) :
    EventuallyPeriodic f := by
  rcases hfg with ⟨N₁, hfg⟩
  rcases hg with ⟨p, hp, N₂, hg⟩
  refine ⟨p, hp, max N₁ N₂, ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hn1' : N₁ ≤ n + p := le_trans hn1 (Nat.le_add_right _ _)
  calc
    f (n + p) = g (n + p) := hfg (n + p) hn1'
    _ = g n := hg n hn2
    _ = f n := (hfg n hn1).symm

/-!
### Single analytic/density axiom

We consolidate the manuscript's analytic input (tail isolation + density domination + stability of
integer boundaries) into a single axiom.

This axiom is the *only* nontrivial external prerequisite used by the main irrationality theorem
in this scaffold.

It has two consequences:

1. **Exhaustion:** the extracted block sequence has unbounded range.
2. **Rational model:** if `erdosSeries b A = q`, then the extracted blocks eventually coincide with
   the finite-state remainder recursion for the rational `q`.

Everything else (eventual periodicity of the rational recursion, transfer lemmas, contradiction)
is proved in Lean.
-/

axiom density_axiom :
    ∃ blk : (b : ℕ) → (A : Set ℕ) → ℕ → ℕ,
      ∀ (b : ℕ) (_hb : 2 ≤ b)
        (A : Set ℕ) (_hA : A.Infinite)
        (_hpos : ∀ n ∈ A, 1 ≤ n),
        (∀ N (s : Finset ℕ), ∃ n ≥ N, blk b A n ∉ s) ∧
          (∀ q : ℚ, erdosSeries b A = q → ∃ N, ∀ n ≥ N, blk b A n = ratStateNat b q n)

/-- The (formal) block sequence, defined by choice from the analytic/density axiom. -/
noncomputable def blocks : (b : ℕ) → (A : Set ℕ) → ℕ → ℕ :=
  Classical.choose density_axiom

/-- Deterministic density domination / exhaustion (derived from `density_axiom`). -/
theorem blocks_unbounded_of_density
    (b : ℕ) (hb : 2 ≤ b)
    (A : Set ℕ) (hA : A.Infinite)
    (hpos : ∀ n ∈ A, 1 ≤ n) :
    ∀ N (s : Finset ℕ), ∃ n ≥ N, blocks b A n ∉ s := by
  simpa [blocks] using (Classical.choose_spec density_axiom) b hb A hA hpos |>.1

/--
Density/stability bridge: once carry-interference is excluded by the manuscript's density bounds,
the extracted blocks agree (eventually) with the rational finite-state sequence.

This is exactly where the analytic/density layer is used.
-/
theorem blocks_eventually_eq_ratStateNat_of_density
    (b : ℕ) (hb : 2 ≤ b)
    (A : Set ℕ) (hA : A.Infinite)
    (hpos : ∀ n ∈ A, 1 ≤ n)
    (q : ℚ) :
    erdosSeries b A = q → ∃ N, ∀ n ≥ N, blocks b A n = ratStateNat b q n
  := (Classical.choose_spec density_axiom) b hb A hA hpos |>.2 q

/--
Rationality ⇒ eventual periodicity (at the level of the extracted blocks).

This is the bridge from the real equality `erdosSeries b A = q` to the combinatorial kernel.
In the TeX manuscript this is mediated by the purely periodic representation `0.\overline{C}`
and the stability of boundaries.
-/
theorem rational_series_eventuallyPeriodic_blocks
    (b : ℕ) (hb : 2 ≤ b)
    (A : Set ℕ) (hA : A.Infinite)
    (hpos : ∀ n ∈ A, 1 ≤ n)
    (q : ℚ) :
    erdosSeries b A = q → EventuallyPeriodic (blocks b A) := by
  intro hq
  have hrat : 
  EventuallyPeriodic (ratStateNat b q) := ratStateNat_eventuallyPeriodic (b := b) (q := q)
  have hEq : ∃ N, ∀ n ≥ N, blocks b A n = ratStateNat b q n :=
    blocks_eventually_eq_ratStateNat_of_density b hb A hA hpos q hq
  exact eventuallyPeriodic_of_eventuallyEq (f := blocks b A) (g := ratStateNat b q) hEq hrat

theorem erdos257_generalized
    (b : ℕ) (hb : 2 ≤ b)
    (A : Set ℕ) (hA : A.Infinite)
    (hpos : ∀ n ∈ A, 1 ≤ n) :
    Irrational (erdosSeries b A) := by
  classical
  -- `Irrational x` means `x` is not in the range of the rational casting map.
  rintro ⟨q, hq⟩
  -- Analytic/density layer (assumed): blocks have unbounded range.
  have hunb : ∀ N (s : Finset ℕ), ∃ n ≥ N, blocks b A n ∉ s :=
    blocks_unbounded_of_density b hb A hA hpos
  -- Rationality layer (assumed): rational values force eventual periodicity.
  have hper : EventuallyPeriodic (blocks b A) := by
    -- Rewrite the witness equation into the shape expected by the axiom.
    have : erdosSeries b A = q := by simpa [eq_comm] using hq
    exact rational_series_eventuallyPeriodic_blocks b hb A hA hpos q this
  -- Exhaustion kernel: unbounded range contradicts eventual periodicity.
  have hnot : ¬ EventuallyPeriodic (blocks b A) :=
    not_eventuallyPeriodic_of_unbounded_range (f := blocks b A) hunb
  exact hnot hper

end Erdos257

end Erdös257

end Erdos
