/-
The address as a sum over the wires.

`wt a k top j` is the weight of wire `j` in the address `val a k gap x` (with
`top = rippleTop k gap`): `sum_wt` says `val a k gap x = Σ_{j=1..m} [x_j] wt j`.
-/
import Mathlib
import ApproxToffoli.Line.Increment

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-- Reindex a sum over the wires `1..m` that satisfy `P` by `i ↦ φ i`, `i < n`. -/
theorem sum_Icc_ind (m : ℕ) (P : ℕ → Prop) [DecidablePred P] (n : ℕ) (φ ψ : ℕ → ℕ)
    (G : ℕ → ℕ)
    (h1 : ∀ i, i < n → 1 ≤ φ i ∧ φ i ≤ m ∧ P (φ i) ∧ ψ (φ i) = i)
    (h2 : ∀ j, 1 ≤ j → j ≤ m → P j → ψ j < n ∧ φ (ψ j) = j) :
    ∑ j ∈ Finset.Icc 1 m, (if P j then G j else 0) = ∑ i ∈ Finset.range n, G (φ i) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' ψ φ ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    exact Finset.mem_range.2 (h2 j hj.1.1 hj.1.2 hj.2).1
  · intro i hi
    have := h1 i (Finset.mem_range.1 hi)
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨this.1, this.2.1⟩, this.2.2.1⟩
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    exact (h2 j hj.1.1 hj.1.2 hj.2).2
  · intro i hi
    exact (h1 i (Finset.mem_range.1 hi)).2.2.2
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    rw [(h2 j hj.1.1 hj.1.2 hj.2).2]

/-- The weight of wire `j` in the address. -/
def wt (a k top j : ℕ) : ℕ :=
  (if j % 2 = 1 ∧ j < 2 * a then 2 ^ ((2 * a - 1 - j) / 2) else 0)
    + 2 ^ a * ((if j % 2 = 0 ∧ 2 ≤ j ∧ j < 2 * k + 2 then 2 ^ ((j - 2) / 2) else 0)
      + (if j = top then 2 ^ k else 0))

theorem wt_split (a k top j : ℕ) (b : Bool) :
    (if b then wt a k top j else 0)
      = (if j % 2 = 1 ∧ j < 2 * a then b.toNat * 2 ^ ((2 * a - 1 - j) / 2) else 0)
        + 2 ^ a * ((if j % 2 = 0 ∧ 2 ≤ j ∧ j < 2 * k + 2 then b.toNat * 2 ^ ((j - 2) / 2)
            else 0)
          + (if j = top then b.toNat * 2 ^ k else 0)) := by
  cases b
  · simp
  · simp [wt]

theorem sum_low (a m : ℕ) (h2a : 2 * a ≤ m) (x : St N) :
    ∑ j ∈ Finset.Icc 1 m, (if j % 2 = 1 ∧ j < 2 * a
        then (wire x j).toNat * 2 ^ ((2 * a - 1 - j) / 2) else 0) = Tval a x := by
  rw [sum_Icc_ind m (fun j => j % 2 = 1 ∧ j < 2 * a) a (fun i => 2 * a - 2 * i - 1)
    (fun j => (2 * a - 1 - j) / 2) (fun j => (wire x j).toNat * 2 ^ ((2 * a - 1 - j) / 2))
    (fun i hi => by dsimp only; omega)
    (fun j h1 h2 hP => by dsimp only at hP ⊢; omega)]
  exact Finset.sum_congr rfl (fun i hi => by
    have := Finset.mem_range.1 hi
    rw [show (2 * a - 1 - (2 * a - 2 * i - 1)) / 2 = i by omega])

theorem sum_high (k m : ℕ) (h2k : 2 * k ≤ m) (x : St N) :
    ∑ j ∈ Finset.Icc 1 m, (if j % 2 = 0 ∧ 2 ≤ j ∧ j < 2 * k + 2
        then (wire x j).toNat * 2 ^ ((j - 2) / 2) else 0)
      = ∑ i ∈ Finset.range k, (wire x (2 * i + 2)).toNat * 2 ^ i := by
  rw [sum_Icc_ind m (fun j => j % 2 = 0 ∧ 2 ≤ j ∧ j < 2 * k + 2) k (fun i => 2 * i + 2)
    (fun j => (j - 2) / 2) (fun j => (wire x j).toNat * 2 ^ ((j - 2) / 2))
    (fun i hi => by dsimp only; omega)
    (fun j h1 h2 hP => by dsimp only at hP ⊢; omega)]
  exact Finset.sum_congr rfl (fun i hi => by
    rw [show (2 * i + 2 - 2) / 2 = i by omega])

/-- **The address is the sum of the weights of the wires that hold a one.** -/
theorem sum_wt (a k : ℕ) (gap : Bool) (m : ℕ) (h2a : 2 * a ≤ m) (h2k : 2 * k ≤ m)
    (ht : rippleTop k gap ≤ m) (x : St N) :
    ∑ j ∈ Finset.Icc 1 m, (if wire x j then wt a k (rippleTop k gap) j else 0)
      = val a k gap x := by
  have hTop : ∑ j ∈ Finset.Icc 1 m,
      (if j = rippleTop k gap then (wire x j).toNat * 2 ^ k else 0)
      = (wire x (rippleTop k gap)).toNat * 2 ^ k := by
    rw [Finset.sum_ite_eq', if_pos]
    rw [Finset.mem_Icc]
    exact ⟨by unfold rippleTop; omega, ht⟩
  simp only [wt_split, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_low a m h2a, sum_high k m h2k, hTop]
  rfl

/-! ### The last address is the all-ones state -/

theorem top_arith (A P L H : ℕ) (hL : L < A) (hH : H < P) :
    L + A * H + 1 = A * P ↔ L + 1 = A ∧ H + 1 = P := by
  constructor
  · intro h
    have h2 : A * (H + 1) ≤ A * P := Nat.mul_le_mul_left A hH
    rw [Nat.mul_add, Nat.mul_one] at h2
    have h3 : L + 1 = A := by omega
    refine ⟨h3, ?_⟩
    have h4 : A * (H + 1) = A * P := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  · rintro ⟨rfl, rfl⟩
    ring

theorem targetVal_top (k : ℕ) (gap : Bool) (x : St N) :
    targetVal k gap x + 1 = 2 ^ (k + 1)
      ↔ (∀ i, i < k → wire x (2 * i + 2) = true) ∧ wire x (rippleTop k gap) = true := by
  have hlt := bsum_lt (fun i => wire x (2 * i + 2)) k
  have hiff := bsum_add_one_eq_iff (fun i => wire x (2 * i + 2)) k
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
  change bsum (fun i => wire x (2 * i + 2)) k + (wire x (rippleTop k gap)).toNat * 2 ^ k + 1
    = 2 ^ (k + 1) ↔ _
  rw [pow_succ, ← hiff]
  cases wire x (rippleTop k gap)
  · simp only [Bool.toNat_false, Bool.false_eq_true, and_false, iff_false]
    omega
  · simp only [Bool.toNat_true, and_true]
    omega

/-- Every wire `1..m` is a low bit, a high bit, or the top bit. -/
theorem wire_cover {a k : ℕ} {gap : Bool} {m j : ℕ} (hka : k ≤ a)
    (hat : 2 * a ≤ rippleTop k gap) (ht : rippleTop k gap = m) (hs : a + (k + 1) = m)
    (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    (j % 2 = 1 ∧ j < 2 * a) ∨ (j % 2 = 0 ∧ 2 ≤ j ∧ j < 2 * k + 2)
      ∨ j = rippleTop k gap := by
  cases gap <;> simp only [rippleTop, Bool.toNat_false, Bool.toNat_true] at * <;> omega

/-- With wire `0` set, the address is the last one iff every wire holds a one. -/
theorem val_top {a k : ℕ} {gap : Bool} (hka : k ≤ a) (hat : 2 * a ≤ rippleTop k gap)
    (ht : rippleTop k gap = N - 1) (hs : a + (k + 1) = N - 1) (hN : 1 ≤ N) (x : St N)
    (h0 : wire x 0 = true) :
    val a k gap x + 1 = 2 ^ (N - 1) ↔ ∀ r : Fin N, x r = true := by
  unfold val
  rw [← hs, pow_add, top_arith _ _ _ _ (Tval_lt a x) (targetVal_lt k gap x), ← allT_iff,
    targetVal_top]
  unfold allT
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hA, hB, hC⟩ r
    rw [← wire_val x r]
    have hr := r.isLt
    by_cases hr0 : r.val = 0
    · rw [hr0]
      exact h0
    rcases wire_cover (j := r.val) hka hat ht hs (by omega) (by omega) with h | h | h
    · have := hA ((2 * a - 1 - r.val) / 2) (by omega)
      rwa [show 2 * a - 2 * ((2 * a - 1 - r.val) / 2) - 1 = r.val by omega] at this
    · have := hB ((r.val - 2) / 2) (by omega)
      rwa [show 2 * ((r.val - 2) / 2) + 2 = r.val by omega] at this
    · rw [h]
      exact hC
  · intro H
    have hw : ∀ j, j < N → wire x j = true := fun j hj => by
      rw [wire_mk x j hj]
      exact H _
    exact ⟨fun i hi => hw _ (by omega), fun i hi => hw _ (by omega), hw _ (by omega)⟩

end Line
