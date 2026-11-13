/-
A conditional on a line with ONE CLEAN HELPER QUBIT and exactly `10 n - 12` CNOTs: the
proof of `Helper.HelperGoal` (`Line/HelperDefs.lean`).

The circuit is `U ; Toffoli(1, 2 → 0) ; U⁻¹`.

* `U = compute n` is a permutation `σ` of the basis states up to phases, it does not touch
  position `0`, and it has `5 n - 10` CNOTs (`spec_compute`, `Line/HelperSweep.lean`).
* If the helper bit is `0`, the conjunction of the bits of `σ x` on positions `1` and `2`
  is the conjunction of the `n` control bits of `x` (`computeW_flags`,
  `Line/HelperFlags.lean`).
* The middle gate is the exact Toffoli (`circMat_toffoliExact`, `Line/HelperToffoli.lean`):
  a diagonal plus a NOT on position `0` times a diagonal (`mono_flip_eq`).
* Conjugating by `U`: the NOT on position `0` commutes with `U⁻¹`, because `U` does not
  touch position `0`, and the two diagonals are permuted by `σ`, the phases of `U`
  cancelling against those of `U⁻¹` (`conj_flip_eq`).  No phase of `U` is ever computed.

The result is `Helper.helper_goal : HelperGoal`.
-/
import Mathlib
import ApproxToffoli.Line.HelperFlags
import ApproxToffoli.Line.HelperToffoli

namespace Helper

open Matrix Line ExactLine

variable {N : ℕ}

/-! ### A controlled NOT as a sum of two terms -/

/-- "Flip bit `q` iff `f`" is: the identity where `f` fails, plus the NOT on `q` where
`f` holds. -/
theorem mono_flip_eq (q : Fin N) (f : St N → Bool)
    (hf : ∀ x b, f (Function.update x q b) = f x) :
    mono (flipPerm q f hf) (fun _ => (1 : ℂ))
      = Matrix.diagonal (fun x => if f x then (0 : ℂ) else 1)
        + oneMat q xGate * Matrix.diagonal (fun x => if f x then (1 : ℂ) else 0) := by
  rw [oneMat_xGate]
  ext y x
  rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_apply]
  simp only [mono, Matrix.of_apply]
  rw [flipPerm_apply, xPerm_apply]
  by_cases hyx : y = x
  · subst hyx
    cases f y <;> simp
  · cases f x <;> simp [hyx]

/-- The same matrix, column by column. -/
theorem flip_col (q : Fin N) (g : St N → Bool) (x y : St N) :
    (Matrix.diagonal (fun x => if g x then (0 : ℂ) else 1)
        + oneMat q xGate * Matrix.diagonal (fun x => if g x then (1 : ℂ) else 0)) y x
      = if y = Function.update x q (xor (x q) (g x)) then 1 else 0 := by
  rw [oneMat_xGate, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_apply]
  simp only [mono, Matrix.of_apply]
  rw [xPerm_apply]
  by_cases hyx : y = x
  · subst hyx
    cases g y <;> simp
  · cases g x <;> simp [hyx]

/-! ### Conjugation -/

/-- **Conjugation.**  Let `M` be a permutation `σ` up to unit phases such that `Mᴴ` commutes
with the NOT on qubit `q`.  Then `Mᴴ · (flip q iff f) · M` is "flip `q` iff `f ∘ σ`":
the phases cancel. -/
theorem conj_flip_eq (q : Fin N) (f : St N → Bool)
    (hf : ∀ x b, f (Function.update x q b) = f x) (σ : Equiv.Perm (St N)) (φ : St N → ℂ)
    (hφ : ∀ x, star (φ x) * φ x = 1)
    (hcomm : oneMat q xGate * (mono σ φ)ᴴ = (mono σ φ)ᴴ * oneMat q xGate) :
    (mono σ φ)ᴴ * (mono (flipPerm q f hf) (fun _ => (1 : ℂ)) * mono σ φ)
      = Matrix.diagonal (fun x => if f (σ x) then (0 : ℂ) else 1)
        + oneMat q xGate * Matrix.diagonal (fun x => if f (σ x) then (1 : ℂ) else 0) := by
  have c1 := conj_mono_diagonal σ φ (fun x => if f x then (0 : ℂ) else 1) hφ
  have c2 := conj_mono_diagonal σ φ (fun x => if f x then (1 : ℂ) else 0) hφ
  rw [mono_flip_eq, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, c1]
  congr 1
  rw [Matrix.mul_assoc (oneMat q xGate), ← Matrix.mul_assoc, ← hcomm, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ (mono σ φ), c2]

/-! ### The controls -/

/-- The conjunction of the bits on the positions `1, 3, 4, ..., n + 1` is "all `n`
controls are one", as `condTarget` states it. -/
theorem controls_eq (n : ℕ) (hn : 2 ≤ n) (x : St (n + 2)) :
    (wire x 1 && (wire x 3 && allB (wire x) 4 (n - 2)))
      = decide (∀ r : Fin (n + 2), r.val ≠ 0 → r.val ≠ 2 → x r = true) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, allB_eq_true_iff]
  constructor
  · rintro ⟨h1, h3, h4⟩ r hr0 hr2
    rw [← wire_val x r]
    by_cases hr1 : r.val = 1
    · rw [hr1]
      exact h1
    · by_cases hr3 : r.val = 3
      · rw [hr3]
        exact h3
      · exact h4 r.val (by omega) (by have := r.isLt; omega)
  · intro h
    have key : ∀ p, p ≠ 0 → p ≠ 2 → p < n + 2 → wire x p = true := by
      intro p hp0 hp2 hp
      rw [wire_mk x p hp]
      exact h ⟨p, hp⟩ hp0 hp2
    exact ⟨key 1 (by omega) (by omega) (by omega), key 3 (by omega) (by omega) (by omega),
      fun p hp1 hp2 => key p (by omega) (by omega) (by omega)⟩

/-! ### The theorem -/

/-- **The action of the circuit.**  A basis state whose helper bit is `0` is sent to
exactly the basis state `condTarget n x`. -/
theorem helper_action (n : ℕ) (hn : 4 ≤ n) (x : St (n + 2))
    (hx : x ⟨2, by omega⟩ = false) :
    circMat (helperCirc n) *ᵥ Pi.single x 1 = Pi.single (condTarget n x) 1 := by
  have hS := spec_compute n hn
  obtain ⟨σ, ⟨φ, hφ, hM⟩, hσ⟩ := hS.sem
  have h2 : 2 < n + 2 := by omega
  -- the NOT on position `0` commutes with `U⁻¹`, which does not touch position `0`
  have hcomm : oneMat (⟨0, by omega⟩ : Fin (n + 2)) xGate * (mono σ φ)ᴴ
      = (mono σ φ)ᴴ * oneMat (⟨0, by omega⟩ : Fin (n + 2)) xGate := by
    have hI : Above 1 (invCirc (compute n)) := circOn_invCirc hS.above
    have hg : (Gate.one (⟨0, by omega⟩ : Fin (n + 2)) xGate).On (fun r => r.val < 1) :=
      Nat.zero_lt_one
    have h := gate_mat_comm_circMat
      (fun (r : Fin (n + 2)) (h1 : r.val < 1) (h2 : 1 ≤ r.val) => by omega) hg hI
    rw [circMat_invCirc, hM] at h
    exact h
  -- the matrix of the circuit
  have hmat : circMat (helperCirc n)
      = Matrix.diagonal (fun y => if (σ y ⟨1, by omega⟩ && σ y ⟨2, h2⟩) then (0 : ℂ) else 1)
        + oneMat (⟨0, by omega⟩ : Fin (n + 2)) xGate
          * Matrix.diagonal
            (fun y => if (σ y ⟨1, by omega⟩ && σ y ⟨2, h2⟩) then (1 : ℂ) else 0) := by
    unfold helperCirc
    rw [circMat_append, circMat_append, circMat_invCirc, hM, circMat_toffoliExact h2]
    exact conj_flip_eq _ _ (both_update h2) σ φ hφ hcomm
  -- the two flags of `σ x`
  have w1 : wire (σ x) 1 = σ x ⟨1, by omega⟩ := wire_mk _ _ _
  have w2 : wire (σ x) 2 = σ x ⟨2, h2⟩ := wire_mk _ _ _
  have hb : (σ x ⟨1, by omega⟩ && σ x ⟨2, h2⟩)
      = decide (∀ r : Fin (n + 2), r.val ≠ 0 → r.val ≠ 2 → x r = true) := by
    rw [← w1, ← w2, hσ x,
      computeW_flags n hn (wire x) (by rw [wire_mk x 2 h2]; exact hx)]
    exact controls_eq n (by omega) x
  funext y
  rw [hmat, Matrix.mulVec_single_one, Matrix.col_apply, flip_col, Pi.single_apply, hb]
  rfl

/-- **A conditional on a line with one clean helper qubit and exactly `10 n - 12` CNOTs.**
For every `n ≥ 4`, the circuit `helperCirc n` on the line of `n + 2` qubits (target `0`,
helper `2`, controls `1, 3, ..., n + 1`; every CNOT between neighbours) has unitary
one-qubit gates and exactly `10 n - 12` CNOTs, and it sends every basis state whose helper
bit is `0` to exactly the basis state in which the target bit is flipped iff all `n`
control bits are one. -/
theorem helper_goal : HelperGoal := by
  intro n hn
  have hS := spec_compute n hn
  have h2 : 2 < n + 2 := by omega
  refine ⟨?_, ?_, fun x hx => helper_action n hn x hx⟩
  · exact unitaryGates_append
      (unitaryGates_append hS.unitary (unitaryGates_toffoliExact h2))
      (unitaryGates_invCirc hS.unitary)
  · unfold helperCirc
    rw [cnots_append, cnots_append, cnots_invCirc, hS.count, cnots_toffoliExact h2]
    omega

end Helper
