/-
The increment on a line: the abstract argument.

The address of a basis state is `val a k gap x = L + 2^a * H`, with the low half
`L = Tval a x` on the odd wires `1, 3, …, 2a-1` and the high half `H = targetVal k gap x`
on the targets of the ripple.  Given three permutations of basis states

* `κ` (the ripple): `H ↦ H + U + [b]` modulo `2^(k+1)`, wire `0` and odd wires unchanged;
* `μ` (the toggle): flips wire `0` iff `L` is all ones;
* `ρ` (the low incrementer): `L ↦ L + 1` modulo `2^a`, flips wire `0` iff `L` is all ones,
  `H` unchanged;

the product `ρ * (κ⁻¹ * (μ * κ))` leaves wire `0` unchanged and, when wire `0` is one,
adds one to the address modulo `2^(a+k+1)` (`inc_core`).
-/
import Mathlib
import ApproxToffoli.Line.RippleAdd
import ApproxToffoli.Line.LowIncMain

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### Arithmetic -/

/-- Undoing the ripple: from `Hw + U + [¬f] ≡ H + U + 1` we get `Hw = H + [f]`. -/
theorem sub_arith (P H Hw U : ℕ) (f : Bool) (hw : Hw < P)
    (h : (Hw + U + (!f).toNat) % P = (H + U + 1) % P) : Hw = (H + f.toNat) % P := by
  cases f
  · have h1 : Hw + (U + 1) ≡ H + (U + 1) [MOD P] := by
      simpa [Nat.ModEq, Nat.add_assoc] using h
    have h2 : Hw ≡ H [MOD P] := Nat.ModEq.add_right_cancel' _ h1
    have h3 : Hw % P = H % P := h2
    rw [Nat.mod_eq_of_lt hw] at h3
    simpa using h3
  · have h1 : Hw + U ≡ (H + 1) + U [MOD P] := by
      have e : H + 1 + U = H + U + 1 := by omega
      simpa [Nat.ModEq, e] using h
    have h2 : Hw ≡ H + 1 [MOD P] := Nat.ModEq.add_right_cancel' _ h1
    have h3 : Hw % P = (H + 1) % P := h2
    rw [Nat.mod_eq_of_lt hw] at h3
    simpa using h3

/-- The low half plus one and the high half plus the carry is the address plus one. -/
theorem val_arith (A P L H : ℕ) (f : Bool) (hL : L < A) (hH : H < P)
    (hf : f = true ↔ L + 1 = A) :
    (L + 1) % A + A * ((H + f.toNat) % P) = (L + A * H + 1) % (A * P) := by
  cases f
  · have hne : L + 1 ≠ A := fun h => by simpa using hf.2 h
    have h1 : L + 1 < A := by omega
    have h2 : A * H + A ≤ A * P := by
      have := Nat.mul_le_mul_left A (show H + 1 ≤ P by omega)
      rwa [Nat.mul_add, Nat.mul_one] at this
    have e0 : H + false.toNat = H := rfl
    rw [Nat.mod_eq_of_lt h1, e0, Nat.mod_eq_of_lt hH, Nat.mod_eq_of_lt (by omega)]
    omega
  · have h1 : L + 1 = A := hf.1 rfl
    have e : L + A * H + 1 = A * (H + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [h1, Nat.mod_self, Nat.zero_add, e, Nat.mul_mod_mul_left, Bool.toNat_true]

/-! ### The registers -/

/-- All bits of the low half are one. -/
def allT (a : ℕ) (x : St N) : Bool :=
  decide (∀ i, i < a → wire x (2 * a - 2 * i - 1) = true)

/-- The address: low half `Tval a`, high half `targetVal k gap`. -/
def val (a k : ℕ) (gap : Bool) (x : St N) : ℕ := Tval a x + 2 ^ a * targetVal k gap x

theorem Tval_lt (a : ℕ) (x : St N) : Tval a x < 2 ^ a :=
  bits_lt (fun i => wire x (2 * a - 2 * i - 1)) a

theorem allT_iff (a : ℕ) (x : St N) : allT a x = true ↔ Tval a x + 1 = 2 ^ a := by
  rw [allT, decide_eq_true_eq]
  exact (bsum_add_one_eq_iff (fun i => wire x (2 * a - 2 * i - 1)) a).symm

theorem targetVal_lt (k : ℕ) (gap : Bool) (x : St N) : targetVal k gap x < 2 ^ (k + 1) := by
  have h1 := bits_lt (fun i => wire x (2 * i + 2)) k
  have h2 := Nat.mul_le_mul_right (2 ^ k) (Bool.toNat_le (wire x (rippleTop k gap)))
  unfold targetVal
  rw [pow_succ]
  linarith

theorem Tval_congr {a : ℕ} {x y : St N}
    (h : ∀ j, j % 2 = 1 → j < 2 * a → wire x j = wire y j) : Tval a x = Tval a y :=
  Finset.sum_congr rfl (fun i hi => by
    have := Finset.mem_range.1 hi
    rw [h _ (by omega) (by omega)])

theorem allT_congr {a : ℕ} {x y : St N}
    (h : ∀ j, j % 2 = 1 → j < 2 * a → wire x j = wire y j) : allT a x = allT a y := by
  unfold allT
  rw [decide_eq_decide]
  exact forall₂_congr (fun i hi => by rw [h _ (by omega) (by omega)])

theorem addendVal_congr {a k : ℕ} (hka : k ≤ a) {x y : St N}
    (h : ∀ j, j % 2 = 1 → j < 2 * a → wire x j = wire y j) :
    addendVal k x = addendVal k y :=
  Finset.sum_congr rfl (fun i hi => by
    have := Finset.mem_range.1 hi
    rw [h _ (by omega) (by omega)])

theorem targetVal_congr {k : ℕ} {gap : Bool} {x y : St N}
    (h : ∀ i, i < k → wire x (2 * i + 2) = wire y (2 * i + 2))
    (ht : wire x (rippleTop k gap) = wire y (rippleTop k gap)) :
    targetVal k gap x = targetVal k gap y := by
  unfold targetVal
  rw [ht]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.1 hi)])

/-! ### The increment -/

/-- **The increment, abstractly.**  `ρ * (κ⁻¹ * (μ * κ))` leaves wire `0` unchanged and,
when wire `0` is one, adds one to the address modulo `2^(a+k+1)`. -/
theorem inc_core {a k : ℕ} {gap : Bool} (hka : k ≤ a) (κ μ ρ : Equiv.Perm (St N))
    (hK0 : ∀ x, wire (κ x) 0 = wire x 0)
    (hKodd : ∀ x j, j % 2 = 1 → j < 2 * a → wire (κ x) j = wire x j)
    (hKadd : ∀ x, targetVal k gap (κ x)
      = (targetVal k gap x + addendVal k x + (wire x 0).toNat) % 2 ^ (k + 1))
    (hM0 : ∀ x, wire (μ x) 0 = xor (wire x 0) (allT a x))
    (hM : ∀ x j, j ≠ 0 → wire (μ x) j = wire x j)
    (hRH : ∀ x, targetVal k gap (ρ x) = targetVal k gap x)
    (hRT : ∀ x, Tval a (ρ x) = (Tval a x + 1) % 2 ^ a)
    (hR0 : ∀ x, wire (ρ x) 0 = xor (wire x 0) (allT a x)) (x : St N) :
    wire ((ρ * (κ⁻¹ * (μ * κ))) x) 0 = wire x 0 ∧
      (wire x 0 = true → val a k gap ((ρ * (κ⁻¹ * (μ * κ))) x)
        = (val a k gap x + 1) % 2 ^ (a + (k + 1))) := by
  obtain ⟨w, hw⟩ : ∃ w, w = κ⁻¹ (μ (κ x)) := ⟨_, rfl⟩
  have hκw : κ w = μ (κ x) := by
    rw [hw]
    exact Equiv.apply_symm_apply κ _
  have hι : (ρ * (κ⁻¹ * (μ * κ))) x = ρ w := by
    rw [hw]
    rfl
  have hodd : ∀ j, j % 2 = 1 → j < 2 * a → wire w j = wire x j := by
    intro j h1 h2
    rw [← hKodd w j h1 h2, hκw, hM _ j (by omega), hKodd x j h1 h2]
  have hf : allT a w = allT a x := allT_congr hodd
  have hf' : allT a (κ x) = allT a x := allT_congr (hKodd x)
  have hw0 : wire w 0 = xor (wire x 0) (allT a x) := by
    rw [← hK0 w, hκw, hM0, hK0, hf']
  have hH : targetVal k gap (μ (κ x)) = targetVal k gap (κ x) :=
    targetVal_congr (fun i _ => hM _ _ (by omega)) (hM _ _ (by unfold rippleTop; omega))
  rw [hι]
  refine ⟨?_, fun hb => ?_⟩
  · rw [hR0, hw0, hf]
    cases wire x 0 <;> cases allT a x <;> rfl
  · have e1 := hKadd w
    rw [hκw, hH, hKadd x, addendVal_congr hka hodd, hw0, hb, Bool.true_xor, Bool.toNat_true] at e1
    have e2 : targetVal k gap w = (targetVal k gap x + (allT a x).toNat) % 2 ^ (k + 1) :=
      sub_arith _ _ _ (addendVal k x) _ (targetVal_lt k gap w) e1.symm
    unfold val
    rw [hRH, hRT, e2, Tval_congr hodd, pow_add 2 a (k + 1)]
    exact val_arith _ _ _ _ _ (Tval_lt a x) (targetVal_lt k gap x) (allT_iff a x)

end Line
