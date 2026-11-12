/-
The Huang–Palsberg circuit `qulin N`: general lemmas for the top-level identity.

Products of diagonal matrices over `forUp`, a permutation between two diagonal matrices,
the phase arithmetic of the roots, and the facts about the qubits `qb N hN i`.
-/
import Mathlib
import ApproxToffoli.Free.QulinInc
import ApproxToffoli.Line.SignConj

namespace Qulin

open Matrix Free ExactLine
open Line (St hGate pGate xGate condMat oneMat signMat)

variable {N : ℕ}

/-! ### Diagonal matrices -/

/-- A `forUp` of diagonal circuits is diagonal, with the product of the entries. -/
theorem circMat_forUp_diagonal (m : ℕ) (f : ℕ → List (Gate N)) (d : ℕ → St N → ℂ)
    (h : ∀ i < m, circMat (f i) = Matrix.diagonal (d i)) :
    circMat (forUp m f) = Matrix.diagonal (fun x => ∏ i ∈ Finset.range m, d i x) := by
  induction m with
  | zero =>
    rw [forUp_zero]
    simp [circMat]
  | succ m ih =>
    rw [forUp_succ, circMat_append, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h m (Nat.lt_succ_self m), Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    rw [Finset.prod_range_succ, mul_comm]

/-- Diagonal, permutation, diagonal, inverse permutation: a diagonal matrix. -/
theorem permMat_diagonal_permMat_diagonal (f g : St N → St N) (hgf : ∀ x, g (f x) = x)
    (d₁ d₂ : St N → ℂ) :
    permMat g * (Matrix.diagonal d₂ * (permMat f * Matrix.diagonal d₁))
      = Matrix.diagonal (fun x => d₁ x * d₂ (f x)) := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single (f x)]
  · rw [Matrix.diagonal_mul, Matrix.mul_diagonal, permMat_apply, permMat_apply, if_pos rfl,
      hgf, Matrix.diagonal_apply]
    by_cases hy : y = x
    · subst hy
      rw [if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg hy, if_neg hy, zero_mul]
  · intro z _ hz
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, permMat_apply, permMat_apply, if_neg hz]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The product of the phases `e (a 2^j)` over the one bits of a register is `e` of
`a` times the value of the register. -/
theorem prod_phase (m : ℕ) (q : ℕ → Fin N) (x : St N) (P : Prop) [Decidable P] (a : ℝ) :
    ∏ j ∈ Finset.range m, (if x (q j) = true ∧ P then e (a * 2 ^ j) else 1)
      = if P then e (a * (regVal m q x : ℝ)) else 1 := by
  induction m with
  | zero =>
    rw [Finset.prod_range_zero, regVal_zero, Nat.cast_zero, mul_zero, e_zero, ite_self]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, regVal_succ]
    by_cases hP : P
    · by_cases hx : x (q m) = true
      · rw [if_pos hP, if_pos ⟨hx, hP⟩, if_pos hP, if_pos hx, ← e_add]
        congr 1
        push_cast
        ring
      · rw [if_pos hP, if_neg (fun h => hx h.1), if_pos hP, if_neg hx, mul_one, Nat.add_zero]
    · rw [if_neg hP, if_neg (fun h => hP h.2), if_neg hP, mul_one]

/-! ### The register: low bit and the rest -/

theorem regVal_tail (m : ℕ) (q : ℕ → Fin N) (x : St N) :
    regVal m (fun j => q (1 + j)) x = regVal (m + 1) q x / 2 := by
  rw [regVal_succ', regVal_congr_reg x (fun i _ => congrArg q (Nat.add_comm 1 i))]
  split_ifs <;> omega

theorem regVal_low (m : ℕ) (q : ℕ → Fin N) (x : St N) :
    x (q 0) = true ↔ regVal (m + 1) q x % 2 = 1 := by
  rw [regVal_succ']
  split_ifs with h
  · simp only [h, true_iff]
    omega
  · rw [Nat.zero_add, Nat.mul_mod_right]
    exact ⟨fun h' => absurd h' h, fun h' => absurd h' (by decide)⟩

/-! ### The phase arithmetic -/

/-- The roots before the increment against the inverse roots after it: `-1` when the
register is all ones, and `1` otherwise. -/
theorem phase_arith (w : ℕ) (hw : 1 ≤ w) (z : ℕ) (hz : z < 2 ^ w) (θ : ℝ)
    (hθ : θ = Real.pi / 2 ^ (w - 1)) :
    e (1 * θ * ((z / 2 : ℕ) : ℝ)) * (if z % 2 = 1 then e θ else 1)
        * e (-1 * θ * (((z + 1) % 2 ^ w / 2 : ℕ) : ℝ))
      = if z = 2 ^ w - 1 then -1 else 1 := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hθ
  have hpos : 0 < 2 ^ v := Nat.pos_of_ne_zero (by positivity)
  rw [pow_succ] at hz ⊢
  by_cases htop : z = 2 ^ v * 2 - 1
  · have h1 : (z + 1) % (2 ^ v * 2) / 2 = 0 := by
      rw [htop, show 2 ^ v * 2 - 1 + 1 = 2 ^ v * 2 by omega, Nat.mod_self]
    have h2 : z % 2 = 1 := by omega
    have h3 : z / 2 = 2 ^ v - 1 := by omega
    rw [if_pos htop, if_pos h2, h1, h3, Nat.cast_zero, mul_zero, e_zero, mul_one, ← e_add,
      ← e_pi]
    congr 1
    rw [hθ, Nat.cast_sub hpos]
    push_cast
    field_simp
    ring
  · have h1 : (z + 1) % (2 ^ v * 2) / 2 = z / 2 + z % 2 := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_neg htop, h1]
    rcases Nat.mod_two_eq_zero_or_one z with h2 | h2
    · rw [if_neg (by omega), h2, Nat.add_zero, mul_one, ← e_add, ← e_zero]
      congr 1
      ring
    · rw [if_pos h2, h2, ← e_add, ← e_add, ← e_zero]
      congr 1
      push_cast
      ring

/-! ### The qubits `qb N hN i` -/

theorem qb_val (hN : 0 < N) {i : ℕ} (hi : i < N) : (qb N hN i).val = i := Nat.mod_eq_of_lt hi

theorem qb_inj (hN : 0 < N) {i j : ℕ} (hi : i < N) (hj : j < N) (h : qb N hN i = qb N hN j) :
    i = j := by
  have h1 := congrArg Fin.val h
  rwa [qb_val hN hi, qb_val hN hj] at h1

theorem qb_ne (hN : 0 < N) {i j : ℕ} (hi : i < N) (hj : j < N) (h : i ≠ j) :
    qb N hN i ≠ qb N hN j := fun e => h (qb_inj hN hi hj e)

theorem qb_self (hN : 0 < N) (r : Fin N) : qb N hN r.val = r :=
  Fin.ext (Nat.mod_eq_of_lt r.isLt)

theorem regW_eq (N : ℕ) : regW N = 2 * (N / 2) - 1 := rfl

/-- The register qubits are distinct. -/
theorem inj_qb (hN : 0 < N) : Inj (2 * (N / 2) - 1) (qb N hN) :=
  fun _ hi _ hj e => qb_inj hN (by omega) (by omega) e

/-- The target is not a register qubit. -/
theorem tgt_ne_qb (hN : 0 < N) : ∀ i < 2 * (N / 2) - 1, qb N hN (N - 1) ≠ qb N hN i :=
  fun _ hi => qb_ne hN (by omega) (by omega) (by omega)

/-- For odd `N` the extra control is not a register qubit. -/
theorem ext_ne_qb (hN : 0 < N) (hodd : ¬ N % 2 = 0) :
    ∀ i < 2 * (N / 2) - 1, qb N hN (N - 2) ≠ qb N hN i :=
  fun _ hi => qb_ne hN (by omega) (by omega) (by omega)

/-- The controls outside the register are one: the target, and for odd `N` the extra
control `N - 2`. -/
def ctl (N : ℕ) (hN : 0 < N) (x : St N) : Prop :=
  (¬ N % 2 = 0 → x (qb N hN (N - 2)) = true) ∧ x (qb N hN (N - 1)) = true

instance (N : ℕ) (hN : 0 < N) (x : St N) : Decidable (ctl N hN x) := by
  unfold ctl
  infer_instance

/-- `ctl` only looks at qubits outside the register. -/
theorem ctl_congr (hN : 0 < N) {x y : St N}
    (h : ∀ r, (∀ i < 2 * (N / 2) - 1, r ≠ qb N hN i) → y r = x r) :
    ctl N hN y ↔ ctl N hN x := by
  unfold ctl
  rw [h _ (tgt_ne_qb hN)]
  by_cases hp : N % 2 = 0
  · simp only [hp, not_true_eq_false, false_imp_iff]
  · rw [h _ (ext_ne_qb hN hp)]

/-- All qubits are one iff the outside controls are one and the register is full. -/
theorem all_one_iff (hN : 0 < N) (x : St N) :
    (∀ r, x r = true) ↔ ctl N hN x ∧ regVal (regW N) (qb N hN) x = 2 ^ regW N - 1 := by
  rw [← regVal_eq_top_iff]
  constructor
  · intro h
    exact ⟨⟨fun _ => h _, h _⟩, fun i _ => h _⟩
  · rintro ⟨⟨hE, ht⟩, hr⟩ r
    rw [← qb_self hN r]
    by_cases h1 : r.val < regW N
    · exact hr _ h1
    · by_cases h2 : r.val = N - 1
      · rw [h2]
        exact ht
      · have h3 : ¬ N % 2 = 0 ∧ r.val = N - 2 := by
          have := r.isLt
          rw [regW_eq] at h1
          omega
        rw [h3.2]
        exact hE h3.1

end Qulin
