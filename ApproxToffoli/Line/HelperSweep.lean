/-
The circuit `U = compute n` of the helper-qubit construction (`Line/HelperDefs.lean`) as a
permutation up to phases with an explicit action on the bits.

* `flW`, `dW`, `eW`, `downW`, `upW`, `botW`: the actions on the bits of the NOT before a
  cell, of the cells `D_k` and `E_k`, of the down and up sweeps and of the bottom.
* `spec_flip`, `spec_down`, `spec_up`, `spec_bottom_even`, `spec_bottom_odd`: the
  corresponding gate lists are permutations up to phases with these actions, they do not
  touch position `0`, and they have `0`, `5 d`, `5 d`, `1` and `11` CNOTs.
* `spec_compute`: `U` has the action `computeW n` and exactly `5 n - 10` CNOTs.

What `computeW n` does to the bits is the subject of `Line/HelperFlags.lean`.
-/
import Mathlib
import ApproxToffoli.Line.HelperCells

namespace Helper

open Matrix Line ExactLine

variable {N : ℕ}

/-! ### Actions on the bits -/

/-- The NOT on position `2 k`, present only for `k ≥ 2`. -/
def flW (k : ℕ) : (ℕ → Bool) → (ℕ → Bool) := if 2 ≤ k then notW (2 * k) else id

/-- The cell `D_k`: NOT on `2 k + 1`, then `x_{2k+1} ^= x_{2k+2} x_{2k+3}`. -/
def dW (k : ℕ) (w : ℕ → Bool) : ℕ → Bool :=
  ccW (2 * k + 1) (2 * k + 3) (2 * k + 2) (notW (2 * k + 1) w)

/-- The cell `E_k`: NOT on `2 k` if `k ≥ 2`, then `x_{2k} ^= x_{2k+1} x_{2k+2}`. -/
def eW (k : ℕ) (w : ℕ → Bool) : ℕ → Bool :=
  ccW (2 * k) (2 * k + 2) (2 * k + 1) (flW k w)

/-- The down sweep: the cells `D_k, D_{k+1}, ..., D_{k+d-1}`, in this order. -/
def downW : ℕ → ℕ → (ℕ → Bool) → (ℕ → Bool)
  | _, 0, w => w
  | k, d + 1, w => downW (k + 1) d (dW k w)

/-- The up sweep: the cells `E_{k+d-1}, ..., E_{k+1}, E_k`, in this order. -/
def upW : ℕ → ℕ → (ℕ → Bool) → (ℕ → Bool)
  | _, 0, w => w
  | k, d + 1, w => eW k (upW (k + 1) d w)

/-- The bottom for even `n`: NOT on `2 K` if `K ≥ 2`, then `x_{2K} ^= x_{2K+1}`. -/
def botEvenW (K : ℕ) (w : ℕ → Bool) : ℕ → Bool := cxW (2 * K + 1) (2 * K) (flW K w)

/-- The bottom for odd `n`. -/
def botOddW (K : ℕ) (w : ℕ → Bool) : ℕ → Bool :=
  eW K (ccW (2 * K + 2) (2 * K + 4) (2 * K + 3)
    (notW (2 * K + 2) (cxW (2 * K + 2) (2 * K + 1) (notW (2 * K + 1) w))))

/-- The action of `U` on the bits, for odd `n`. -/
def computeOddW (K : ℕ) (w : ℕ → Bool) : ℕ → Bool :=
  upW 1 (K - 1) (botOddW K (downW 1 (K - 1) (andW w)))

/-- The action of `U` on the bits, for even `n`. -/
def computeEvenW (K : ℕ) (w : ℕ → Bool) : ℕ → Bool :=
  upW 1 (K - 1) (botEvenW K (downW 1 K (andW w)))

/-- The action of `U = compute n` on the bits; `K = (n - 2) / 2`. -/
def computeW (n : ℕ) : (ℕ → Bool) → (ℕ → Bool) :=
  if n % 2 = 1 then computeOddW ((n - 2) / 2) else computeEvenW ((n - 2) / 2)

/-! ### The stages of `U` -/

theorem spec_flip (k : ℕ) (h : 2 * k < N) : Spec (flip N k) (flW k) 0 := by
  unfold flip flW
  split_ifs
  · exact spec_x (2 * k) (by omega) h
  · exact spec_nil

/-- The cell `D_k`; 5 CNOTs. -/
theorem spec_dCell (k : ℕ) (h : 2 * k + 3 < N) :
    Spec (uAt N (2 * k + 1) xGate ++ toffoliEnd N (2 * k + 1) (2 * k + 2) (2 * k + 3))
      (dW k) 5 :=
  ((spec_x (2 * k + 1) (by omega) (by omega)).append
    (spec_toffoliEnd (2 * k + 1) (2 * k + 2) (2 * k + 3) (by omega) (by omega) (by omega)
      (by omega) (by omega) h (by omega) (by omega) (by omega))).cast (fun _ => rfl)
    (by omega)

/-- The down sweep of `d` cells starting at `D_k`; `5 d` CNOTs. -/
theorem spec_down (d k : ℕ) (h : 2 * (k + d) + 1 < N) :
    Spec (down N k d) (downW k d) (5 * d) := by
  induction d generalizing k with
  | zero => exact spec_nil
  | succ d ih =>
    have h1 := spec_dCell (N := N) k (by omega)
    have h2 := ih (k + 1) (by omega)
    exact (h1.append h2).cast (fun _ => rfl) (by omega)

/-- The up sweep of `d` cells ending with `E_k`; `5 d` CNOTs. -/
theorem spec_up (d k : ℕ) (h1 : 1 ≤ k) (h : 2 * (k + d) < N) :
    Spec (up N k d) (upW k d) (5 * d) := by
  induction d generalizing k with
  | zero => exact spec_nil
  | succ d ih =>
    have h2 := ih (k + 1) (by omega) (by omega)
    have h3 := spec_flip (N := N) k (by omega)
    have h4 := spec_toffoliEnd (N := N) (2 * k) (2 * k + 1) (2 * k + 2) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    exact ((h2.append h3).append h4).cast (fun _ => rfl) (by omega)

/-- The bottom for even `n`; 1 CNOT. -/
theorem spec_bottom_even (K : ℕ) (h1 : 1 ≤ K) (h : 2 * K + 1 < N) :
    Spec (bottom N false K) (botEvenW K) 1 :=
  ((spec_flip K (by omega)).append
    (spec_cx (2 * K + 1) (2 * K) (by omega) (by omega) h (by omega) (by omega))).cast
    (fun _ => rfl) (by omega)

/-- The bottom for odd `n`; 11 CNOTs. -/
theorem spec_bottom_odd (K : ℕ) (h1 : 1 ≤ K) (h : 2 * K + 4 < N) :
    Spec (bottom N true K) (botOddW K) 11 :=
  ((((((spec_x (2 * K + 1) (by omega) (by omega)).append
    (spec_cx (2 * K + 2) (2 * K + 1) (by omega) (by omega) (by omega) (by omega)
      (by omega))).append
    (spec_x (2 * K + 2) (by omega) (by omega))).append
    (spec_toffoliEnd (2 * K + 2) (2 * K + 3) (2 * K + 4) (by omega) (by omega) (by omega)
      (by omega) (by omega) h (by omega) (by omega) (by omega))).append
    (spec_flip K (by omega))).append
    (spec_toffoliEnd (2 * K) (2 * K + 1) (2 * K + 2) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))).cast
    (fun _ => rfl) (by omega)

/-! ### The circuit `U` -/

/-- **The circuit `U`** is a permutation up to phases that acts on the bits as
`computeW n`; it does not touch position `0` and it has exactly `5 n - 10` CNOTs. -/
theorem spec_compute (n : ℕ) (hn : 4 ≤ n) : Spec (compute n) (computeW n) (5 * n - 10) := by
  have hA := spec_andInPlace (N := n + 2) (by omega)
  have hU := spec_up (N := n + 2) ((n - 2) / 2 - 1) 1 le_rfl (by omega)
  unfold compute computeW
  by_cases hodd : n % 2 = 1
  · have hD := spec_down (N := n + 2) ((n - 2) / 2 - 1) 1 (by omega)
    have hB := spec_bottom_odd (N := n + 2) ((n - 2) / 2) (by omega) (by omega)
    rw [if_pos hodd, if_pos hodd, decide_eq_true hodd]
    exact (((hA.append hD).append hB).append hU).cast (fun _ => rfl) (by omega)
  · have hD := spec_down (N := n + 2) ((n - 2) / 2) 1 (by omega)
    have hB := spec_bottom_even (N := n + 2) ((n - 2) / 2) (by omega) (by omega)
    rw [if_neg hodd, if_neg hodd, decide_eq_false hodd]
    exact (((hA.append hD).append hB).append hU).cast (fun _ => rfl) (by omega)

end Helper
