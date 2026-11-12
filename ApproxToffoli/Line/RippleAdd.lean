/-
The ripple-carry adder on a line: statements for the ripple with carry-in on wire `0`.

`ripple N k gap` uses wires `0 .. 2k+1` (`gap = false`) or `0 .. 2k+2` (`gap = true`):
carry-in `b` on wire `0`, addend bits `u_i` on wires `2i+1`, target bits `h_i` on wires
`2i+2` (`i < k`), top target bit on wire `rippleTop k gap`.

* `cnots_ripple`: `13 k + 1` CNOTs, or `13 k + 4` with a gap.
* `circMat_ripple`: the matrix is the permutation `ripplePerm N k gap` up to phases.
* `ripplePerm_target`, `ripplePerm_top`, `ripplePerm_other`: the permutation on bits.
* `ripple_add`: the target register receives `target + addend + carry-in` mod `2^(k+1)`.
* `circMat_invCirc_ripple`: the inverse circuit is the inverse permutation up to phases.
-/
import Mathlib
import ApproxToffoli.Line.Ripple

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-- **The ripple** with `k` cells and carry-in on wire `0`. -/
noncomputable def ripple (N k : ℕ) (gap : Bool) : List (Gate N) := rippleAt N 0 k gap

/-- The basis permutation of the ripple. -/
def ripplePerm (N k : ℕ) (gap : Bool) : Equiv.Perm (St N) := ripplePermAt N 0 k gap

/-- The top target wire: `2k + 1`, or `2k + 2` when there is a gap. -/
def rippleTop (k : ℕ) (gap : Bool) : ℕ := 2 * k + 1 + gap.toNat

theorem rippleTop_false (k : ℕ) : rippleTop k false = 2 * k + 1 := rfl

theorem rippleTop_true (k : ℕ) : rippleTop k true = 2 * k + 2 := rfl

theorem rippleTop_lt {k : ℕ} {gap : Bool} (hN : rippleTop k gap < N) :
    0 + 2 * k + 1 + gap.toNat < N := by
  rw [Nat.zero_add]
  exact hN

/-- The carries: `c_0 = x 0` and `c_{i+1} = maj c_i u_i h_i`. -/
def rcarry (x : St N) : ℕ → Bool
  | 0 => wire x 0
  | i + 1 => maj (rcarry x i) (wire x (2 * i + 1)) (wire x (2 * i + 2))

theorem rcarry_zero (x : St N) : rcarry x 0 = wire x 0 := rfl

theorem rcarry_succ (x : St N) (i : ℕ) :
    rcarry x (i + 1) = maj (rcarry x i) (wire x (2 * i + 1)) (wire x (2 * i + 2)) := rfl

theorem rcarry_eq (x : St N) (i : ℕ) : rcarry x i = carry x 0 i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change maj (rcarry x i) (wire x (2 * i + 1)) (wire x (2 * i + 2))
      = maj (carry x 0 i) (wire x (0 + 2 * i + 1)) (wire x (0 + 2 * i + 2))
    rw [ih, Nat.zero_add]

/-! ### (a) Cost and unitarity -/

/-- The ripple has `13 k + 1` CNOTs, or `13 k + 4` with a gap. -/
theorem cnots_ripple (k : ℕ) (gap : Bool) (hN : rippleTop k gap < N) :
    cnots (ripple N k gap) = 13 * k + (if gap then 4 else 1) := by
  rw [ripple, cnots_rippleAt 0 k gap (rippleTop_lt hN)]
  cases gap <;> rfl

theorem unitaryGates_ripple (N k : ℕ) (gap : Bool) : UnitaryGates (ripple N k gap) :=
  unitaryGates_rippleAt N 0 k gap

/-! ### (b) The ripple is a permutation up to phases, and its action on bits -/

/-- The ripple is the permutation `ripplePerm` up to phases of modulus one. -/
theorem circMat_ripple (N k : ℕ) (gap : Bool) :
    ∃ φ : St N → ℂ, (∀ x, star (φ x) * φ x = 1) ∧
      circMat (ripple N k gap) = mono (ripplePerm N k gap) φ :=
  umono_rippleAt N 0 k gap

/-- Target wire `2i + 2` receives the sum bit `h_i ⊕ u_i ⊕ c_i`. -/
theorem ripplePerm_target (k : ℕ) (gap : Bool) (hN : rippleTop k gap < N) (x : St N) (i : ℕ)
    (hi : i < k) :
    wire (ripplePerm N k gap x) (2 * i + 2)
      = xor (xor (wire x (2 * i + 2)) (wire x (2 * i + 1))) (rcarry x i) := by
  have h := ripple_target 0 k gap (rippleTop_lt hN) x i hi
  simp only [Nat.zero_add] at h
  rw [rcarry_eq]
  exact h

/-- The top wire receives the last carry: `y top = x top ⊕ c_k`. -/
theorem ripplePerm_top (k : ℕ) (gap : Bool) (hN : rippleTop k gap < N) (x : St N) :
    wire (ripplePerm N k gap x) (rippleTop k gap)
      = xor (wire x (rippleTop k gap)) (rcarry x k) := by
  have h := ripple_top 0 k gap (rippleTop_lt hN) x
  simp only [Nat.zero_add] at h
  rw [rcarry_eq]
  exact h

/-- Every wire other than the targets `2i + 2` (`i < k`) and the top wire is unchanged:
wire `0`, the odd wires `2i + 1`, the gap wire, and all wires above the top. -/
theorem ripplePerm_other (k : ℕ) (gap : Bool) (hN : rippleTop k gap < N) (x : St N) (j : ℕ)
    (hj : ∀ i < k, j ≠ 2 * i + 2) (ht : j ≠ rippleTop k gap) :
    wire (ripplePerm N k gap x) j = wire x j := by
  refine ripple_other 0 k gap (rippleTop_lt hN) x j (fun i hi => ?_) ?_
  · rw [Nat.zero_add]
    exact hj i hi
  · rw [Nat.zero_add]
    exact ht

/-! ### (d) The inverse circuit -/

/-- The inverse ripple is the inverse permutation up to phases of modulus one. -/
theorem circMat_invCirc_ripple (N k : ℕ) (gap : Bool) :
    ∃ φ : St N → ℂ, (∀ x, star (φ x) * φ x = 1) ∧
      circMat (invCirc (ripple N k gap)) = mono (ripplePerm N k gap)⁻¹ φ := by
  rw [circMat_invCirc]
  exact (umono_rippleAt N 0 k gap).conjTranspose

/-! ### (c) Ripple-carry addition is addition -/

/-- The value of the target register: `Σ_{i<k} [h_i] 2^i + [x top] 2^k`. -/
def targetVal (k : ℕ) (gap : Bool) (x : St N) : ℕ :=
  ∑ i ∈ Finset.range k, (wire x (2 * i + 2)).toNat * 2 ^ i
    + (wire x (rippleTop k gap)).toNat * 2 ^ k

/-- The value of the addend register: `Σ_{i<k} [u_i] 2^i`. -/
def addendVal (k : ℕ) (x : St N) : ℕ :=
  ∑ i ∈ Finset.range k, (wire x (2 * i + 1)).toNat * 2 ^ i

theorem bits_lt (f : ℕ → Bool) (k : ℕ) :
    ∑ i ∈ Finset.range k, (f i).toNat * 2 ^ i < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h2 := Nat.mul_le_mul_right (2 ^ k) (Bool.toNat_le (f k))
    linarith

/-- The full adder: sum bit plus twice the carry is the sum of the three bits. -/
theorem full_adder (h u c : Bool) :
    (xor (xor h u) c).toNat + 2 * (maj c u h).toNat = h.toNat + u.toNat + c.toNat := by
  cases h <;> cases u <;> cases c <;> rfl

/-- The sum bits and the last carry represent `target + addend + carry-in`. -/
theorem adder_sum (x : St N) (k : ℕ) :
    ∑ i ∈ Finset.range k,
        (xor (xor (wire x (2 * i + 2)) (wire x (2 * i + 1))) (rcarry x i)).toNat * 2 ^ i
        + (rcarry x k).toNat * 2 ^ k
      = ∑ i ∈ Finset.range k, (wire x (2 * i + 2)).toNat * 2 ^ i
        + ∑ i ∈ Finset.range k, (wire x (2 * i + 1)).toNat * 2 ^ i + (wire x 0).toNat := by
  induction k with
  | zero => simp [rcarry]
  | succ k ih =>
    have hP := congrArg (fun n => n * 2 ^ k)
      (full_adder (wire x (2 * k + 2)) (wire x (2 * k + 1)) (rcarry x k))
    dsimp only at hP
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, rcarry_succ,
      pow_succ]
    linarith

theorem add_bits_mod (A P : ℕ) (hA : A < P) (t c : Bool) :
    A + (xor t c).toNat * P = (A + c.toNat * P + t.toNat * P) % (2 * P) := by
  cases t <;> cases c
  · change A + 0 * P = (A + 0 * P + 0 * P) % (2 * P)
    rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  · change A + 1 * P = (A + 1 * P + 0 * P) % (2 * P)
    rw [Nat.zero_mul, Nat.add_zero, Nat.one_mul, Nat.mod_eq_of_lt (by omega)]
  · change A + 1 * P = (A + 0 * P + 1 * P) % (2 * P)
    rw [Nat.zero_mul, Nat.add_zero, Nat.one_mul, Nat.mod_eq_of_lt (by omega)]
  · change A + 0 * P = (A + 1 * P + 1 * P) % (2 * P)
    have e : A + 1 * P + 1 * P = A + 2 * P := by omega
    rw [e, Nat.add_mod_right, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]

/-- **Ripple-carry addition is addition.**  The ripple replaces the target register
`H` by `H + U + b` modulo `2^(k+1)`, where `U` is the addend and `b` the carry-in. -/
theorem ripple_add (k : ℕ) (gap : Bool) (hN : rippleTop k gap < N) (x : St N) :
    targetVal k gap (ripplePerm N k gap x)
      = (targetVal k gap x + addendVal k x + (wire x 0).toNat) % 2 ^ (k + 1) := by
  have hs : ∑ i ∈ Finset.range k, (wire (ripplePerm N k gap x) (2 * i + 2)).toNat * 2 ^ i
      = ∑ i ∈ Finset.range k,
          (xor (xor (wire x (2 * i + 2)) (wire x (2 * i + 1))) (rcarry x i)).toNat * 2 ^ i :=
    Finset.sum_congr rfl (fun i hi => by
      rw [ripplePerm_target k gap hN x i (Finset.mem_range.1 hi)])
  have hA := bits_lt (fun i => xor (xor (wire x (2 * i + 2)) (wire x (2 * i + 1))) (rcarry x i)) k
  have hadd := adder_sum x k
  have hmod := add_bits_mod _ _ hA (wire x (rippleTop k gap)) (rcarry x k)
  unfold targetVal addendVal
  rw [hs, ripplePerm_top k gap hN x, hmod, pow_succ, Nat.mul_comm (2 ^ k) 2]
  congr 1
  linarith

end Line
