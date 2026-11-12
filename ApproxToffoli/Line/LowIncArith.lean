/-
Bit sequences for the low incrementer: carries, complements and the arithmetic identity.

For bit sequences `s t : ℕ → Bool`:

* `gcarry s t i`: the carries of the addition `s + t` (no carry-in);
* `bsum f k`: the number with bits `f 0, …, f (k-1)`;
* `gadder_sum`: the sum bits and the last carry represent `s + t`;
* `gcarry_not`: the carries of the complemented sequences;
* `inc_bits`: complementing the inputs and the outputs of an addition is the addition
  followed by an increment modulo `2^k`.
-/
import Mathlib
import ApproxToffoli.Line.RippleAdd

namespace Line

/-- The carries of the addition of two bit sequences: `c_0 = 0`,
`c_{i+1} = maj (s_i, t_i, c_i)`. -/
def gcarry (s t : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => maj (s i) (t i) (gcarry s t i)

theorem gcarry_zero (s t : ℕ → Bool) : gcarry s t 0 = false := rfl

theorem gcarry_succ (s t : ℕ → Bool) (i : ℕ) :
    gcarry s t (i + 1) = maj (s i) (t i) (gcarry s t i) := rfl

theorem gcarry_congr {s t s' t' : ℕ → Bool} (k : ℕ) (hs : ∀ i, i < k → s i = s' i)
    (ht : ∀ i, i < k → t i = t' i) : gcarry s t k = gcarry s' t' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [gcarry_succ, gcarry_succ, hs k (by omega), ht k (by omega),
      ih (fun i hi => hs i (by omega)) (fun i hi => ht i (by omega))]

/-- All of the first `j` positions propagate a carry: `s_l ≠ t_l` for `l < j`. -/
def gprop (s t : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | j + 1 => gprop s t j && xor (s j) (t j)

theorem gprop_eq_true_iff (s t : ℕ → Bool) (j : ℕ) :
    gprop s t j = true ↔ ∀ l, l < j → xor (s l) (t l) = true := by
  induction j with
  | zero => simp [gprop]
  | succ j ih =>
    change (gprop s t j && xor (s j) (t j)) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h1⟩ l hl
      by_cases h : l = j
      · rw [h]
        exact h1
      · exact h0 l (by omega)
    · intro h
      exact ⟨fun l hl => h l (by omega), h j (by omega)⟩

/-- **The carries of the complemented sequences.** -/
theorem gcarry_not (s t : ℕ → Bool) (j : ℕ) :
    gcarry (fun i => !s i) (fun i => !t i) j = !(xor (gcarry s t j) (gprop s t j)) := by
  have e : ∀ a b c g : Bool, maj (!a) (!b) (!(xor c g)) = !(xor (maj a b c) (g && xor a b)) := by
    decide
  induction j with
  | zero => rfl
  | succ j ih =>
    change maj (!s j) (!t j) (gcarry (fun i => !s i) (fun i => !t i) j)
      = !(xor (maj (s j) (t j) (gcarry s t j)) (gprop s t j && xor (s j) (t j)))
    rw [ih]
    exact e _ _ _ _

/-! ### Numbers from bits -/

/-- The number with bits `f 0, …, f (k-1)`. -/
def bsum (f : ℕ → Bool) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (f i).toNat * 2 ^ i

theorem bsum_zero (f : ℕ → Bool) : bsum f 0 = 0 := rfl

theorem bsum_succ (f : ℕ → Bool) (k : ℕ) :
    bsum f (k + 1) = bsum f k + (f k).toNat * 2 ^ k := Finset.sum_range_succ _ _

theorem bsum_lt (f : ℕ → Bool) (k : ℕ) : bsum f k < 2 ^ k := bits_lt f k

/-- The complemented bits: `(2^k - 1) - bsum f k`. -/
theorem bsum_not (f : ℕ → Bool) (k : ℕ) : bsum (fun i => !f i) k + bsum f k + 1 = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : (!f k).toNat + (f k).toNat = 1 := by cases f k <;> rfl
    have e' := congrArg (fun n => n * 2 ^ k) e
    dsimp only at e'
    rw [bsum_succ, bsum_succ, pow_succ]
    linarith

/-- All `k` bits are one iff the number is `2^k - 1`. -/
theorem bsum_add_one_eq_iff (f : ℕ → Bool) (k : ℕ) :
    bsum f k + 1 = 2 ^ k ↔ ∀ i, i < k → f i = true := by
  induction k with
  | zero => simp [bsum_zero]
  | succ k ih =>
    have hlt := bsum_lt f k
    rw [bsum_succ, pow_succ]
    constructor
    · intro h i hi
      have hk : f k = true := by
        cases hf : f k
        · rw [hf] at h
          change bsum f k + 0 * 2 ^ k + 1 = 2 ^ k * 2 at h
          omega
        · rfl
      rw [hk] at h
      change bsum f k + 1 * 2 ^ k + 1 = 2 ^ k * 2 at h
      by_cases hik : i = k
      · rw [hik]
        exact hk
      · exact ih.1 (by omega) i (by omega)
    · intro h
      have h1 := ih.2 (fun i hi => h i (by omega))
      rw [h k (by omega)]
      change bsum f k + 1 * 2 ^ k + 1 = 2 ^ k * 2
      omega

theorem full_adder' (s t c : Bool) :
    (xor (xor s t) c).toNat + 2 * (maj s t c).toNat = s.toNat + t.toNat + c.toNat := by
  cases s <;> cases t <;> cases c <;> rfl

/-- **The sum bits and the last carry represent the sum.** -/
theorem gadder_sum (s t : ℕ → Bool) (k : ℕ) :
    bsum (fun i => xor (xor (s i) (t i)) (gcarry s t i)) k + (gcarry s t k).toNat * 2 ^ k
      = bsum s k + bsum t k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hP := congrArg (fun n => n * 2 ^ k) (full_adder' (s k) (t k) (gcarry s t k))
    dsimp only at hP
    rw [bsum_succ, bsum_succ, bsum_succ, gcarry_succ, pow_succ]
    linarith

/-! ### Complement, add, complement is add, increment -/

/-- The arithmetic core.  `R + c B = U` is an addition with result `R` and carry `c`;
`R' + c' B = 2B - 2 - U` is the addition of the complemented inputs. -/
theorem inc_arith (B R R' U : ℕ) (c c' : Bool) (hR : R < B) (hR' : R' < B)
    (h1 : R + c.toNat * B = U) (h2 : R' + c'.toNat * B + U + 2 = 2 * B) :
    B - 1 - R' = (R + 1) % B ∧ (!c') = xor c (decide (R + 1 = B)) := by
  cases c <;> cases c' <;>
    simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, add_zero] at h1 h2
  · have hRB : R + 1 = B := by omega
    refine ⟨?_, ?_⟩
    · rw [hRB, Nat.mod_self]
      omega
    · simp [hRB]
  · have hlt : R + 1 < B := by omega
    have hne : ¬ R + 1 = B := by omega
    refine ⟨?_, ?_⟩
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · simp [hne]
  · have hlt : R + 1 < B := by omega
    have hne : ¬ R + 1 = B := by omega
    refine ⟨?_, ?_⟩
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · simp [hne]
  · exfalso
    omega

/-- The sum bit at position `i` of the addition `s + t`. -/
def gsumBit (s t : ℕ → Bool) (i : ℕ) : Bool := xor (xor (s i) (t i)) (gcarry s t i)

/-- **Complement the inputs, add, complement the outputs: this is add, then increment.**
With `r` the sum bits of `s + t` and `r'` the sum bits of `¬s + ¬t` (on `k` bits):
the number `¬r'` is `r + 1` modulo `2^k`, and the complemented last carry of `¬s + ¬t` is
the last carry of `s + t` flipped iff all `r_i` are one. -/
theorem inc_bits (s t : ℕ → Bool) (k : ℕ) :
    bsum (fun i => !gsumBit (fun i => !s i) (fun i => !t i) i) k
        = (bsum (gsumBit s t) k + 1) % 2 ^ k
      ∧ (!gcarry (fun i => !s i) (fun i => !t i) k)
        = xor (gcarry s t k) (decide (∀ i, i < k → gsumBit s t i = true)) := by
  have h1 := gadder_sum s t k
  have h2 := gadder_sum (fun i => !s i) (fun i => !t i) k
  have hs := bsum_not s k
  have ht := bsum_not t k
  have hr := bsum_not (gsumBit (fun i => !s i) (fun i => !t i)) k
  have hd : decide (bsum (gsumBit s t) k + 1 = 2 ^ k)
      = decide (∀ i, i < k → gsumBit s t i = true) :=
    decide_eq_decide.2 (bsum_add_one_eq_iff _ k)
  have key := inc_arith (2 ^ k) (bsum (gsumBit s t) k)
    (bsum (gsumBit (fun i => !s i) (fun i => !t i)) k) (bsum s k + bsum t k)
    (gcarry s t k) (gcarry (fun i => !s i) (fun i => !t i) k) (bsum_lt _ k) (bsum_lt _ k) h1
    (by
      change bsum (gsumBit (fun i => !s i) (fun i => !t i)) k + _ = _ at h2
      rw [h2]
      omega)
  rw [← hd, ← key.1, ← key.2]
  exact ⟨by omega, rfl⟩

end Line
