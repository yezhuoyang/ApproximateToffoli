/-
The exact Toffoli gate on three adjacent qubits of a line (the cell `F` of the paper), as
it is written in `Line/HelperDefs.lean` (`toffoliExact`).

* `signCirc a b c` (8 CNOTs): the sign `(-1)^(x_a x_b x_c)`, by four sweeps
  `CX(a, b) ; CX(b, c)` and seven phase gates `P(± π/4)`.
* `circMat_signCirc`: its matrix is that diagonal sign.
* `h_sign_h`: conjugating a controlled sign by Hadamard gates on the target gives the
  controlled NOT, exactly.
* `circMat_toffoliExact`: the matrix of `toffoliExact N 0 1 2` is the permutation matrix
  that flips bit `0` iff bits `1` and `2` are both one (no phases); it has 8 CNOTs.
-/
import Mathlib
import ApproxToffoli.Line.HelperCells
import ApproxToffoli.Line.SignConj

namespace Helper

open Matrix Line ExactLine

variable {N : ℕ}

/-! ### The sign -/

/-- The sign `(-1)^(x_a x_b x_c)` on three qubits `a, b, c`, where `b` is a neighbour of
both: 8 CNOTs, in four sweeps `CX(a, b) ; CX(b, c)`. -/
noncomputable def signCirc (a b c : Fin N) (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hbc : b.val + 1 = c.val ∨ c.val + 1 = b.val) : List (Gate N) :=
  [.one a (pGate (Real.pi / 4)), .one b (pGate (Real.pi / 4)), .one c (pGate (Real.pi / 4)),
   .cx a b hab, .one b (pGate (-Real.pi / 4)), .cx b c hbc, .one c (pGate (Real.pi / 4)),
   .cx a b hab, .cx b c hbc, .one c (pGate (-Real.pi / 4)),
   .cx a b hab, .cx b c hbc, .one c (pGate (-Real.pi / 4)),
   .cx a b hab, .cx b c hbc]

theorem cnots_signCirc (a b c : Fin N) (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hbc : b.val + 1 = c.val ∨ c.val + 1 = b.val) : cnots (signCirc a b c hab hbc) = 8 := rfl

theorem unitaryGates_signCirc (a b c : Fin N) (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hbc : b.val + 1 = c.val ∨ c.val + 1 = b.val) :
    UnitaryGates (signCirc a b c hab hbc) := by
  unfold signCirc
  repeat first
    | exact unitaryGates_nil
    | apply unitaryGates_cons_cx
    | apply unitaryGates_cons_one _ (pGate_unitary _)

theorem cxPerm_eq_cxFun (c t : Fin N) (h : c ≠ t) (x : St N) : cxPerm c t h x = cxFun c t x :=
  rfl

theorem cxFun_self (c t : Fin N) (x : St N) : cxFun c t x t = xor (x t) (x c) := by
  simp [cxFun]

theorem cxFun_of_ne (c t : Fin N) {r : Fin N} (h : r ≠ t) (x : St N) :
    cxFun c t x r = x r := by
  simp [cxFun, Function.update_of_ne h]

/-- Two sweeps `CX(a, b) ; CX(b, c)` are `CX(a, c)`. -/
theorem sweep_sweep {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : St N) :
    cxFun b c (cxFun a b (cxFun b c (cxFun a b x))) = cxFun a c x := by
  funext r
  by_cases hrc : r = c
  · subst hrc
    simp only [cxFun_self, cxFun_of_ne a b hbc.symm, cxFun_of_ne a b hab, cxFun_of_ne b r hbc,
      cxFun_of_ne b r hac]
    cases x r <;> cases x b <;> cases x a <;> rfl
  · by_cases hrb : r = b
    · subst hrb
      simp only [cxFun_self, cxFun_of_ne a r hab, cxFun_of_ne r c hrc, cxFun_of_ne r c hac,
        cxFun_of_ne a c hrc]
      cases x r <;> cases x a <;> rfl
    · simp only [cxFun_of_ne _ _ hrc, cxFun_of_ne _ _ hrb]

theorem mono_congr {ι : Type*} [DecidableEq ι] {σ τ : Equiv.Perm ι}
    {φ ψ : ι → ℂ} (h1 : ∀ x, σ x = τ x) (h2 : ∀ x, φ x = ψ x) : mono σ φ = mono τ ψ := by
  rw [Equiv.ext h1, funext h2]

theorem ite_e (b : Bool) (t : ℝ) :
    (if b = true then e t else (1 : ℂ)) = e (if b = true then t else 0) := by
  cases b <;> simp [e_zero]

theorem e_eq_one {s : ℝ} (h : s = 0) : e s = 1 := by rw [h, e_zero]

theorem e_eq_neg_one {s : ℝ} (h : s = Real.pi) : e s = -1 := by rw [h, e_pi]

/-- **The sign.**  The matrix of `signCirc a b c` is the diagonal with `-1` exactly on the
basis states in which the three bits are one. -/
theorem circMat_signCirc (a b c : Fin N) (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hbc : b.val + 1 = c.val ∨ c.val + 1 = b.val) (hac : a ≠ c) :
    circMat (signCirc a b c hab hbc)
      = Matrix.diagonal (fun x => if (x b && x c) && x a then (-1 : ℂ) else 1) := by
  have nab : a ≠ b := adj_ne hab
  have nbc : b ≠ c := adj_ne hbc
  have e1 : ∀ (p : Fin N) (y : St N), cxFun p c y a = y a := fun p y => cxFun_of_ne p c hac y
  have e2 : ∀ (p : Fin N) (y : St N), cxFun p c y b = y b := fun p y => cxFun_of_ne p c nbc y
  have e3 : ∀ (p : Fin N) (y : St N), cxFun p b y a = y a := fun p y => cxFun_of_ne p b nab y
  have e4 : ∀ (p : Fin N) (y : St N), cxFun p b y c = y c :=
    fun p y => cxFun_of_ne p b nbc.symm y
  rw [← mono_one_eq_diagonal]
  simp only [signCirc, circMat, Gate.mat, Matrix.one_mul, oneMat_pGate, mono_mul]
  apply mono_congr
  · intro x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, cxPerm_eq_cxFun,
      sweep_sweep nab hac nbc]
    exact cxFun_involutive a c hac x
  · intro x
    simp only [Equiv.Perm.one_apply, cxPerm_eq_cxFun, one_mul, mul_one, ite_e, ← e_add,
      sweep_sweep nab hac nbc, cxFun_self, e1, e2, e3, e4]
    generalize x a = u
    generalize x b = v
    generalize x c = w
    cases u <;> cases v <;> cases w <;>
      simp only [Bool.bne_false, Bool.bne_true, bne_self_eq_false, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte, add_zero, zero_add, Bool.and_self, Bool.and_true,
        Bool.and_false] <;>
      first | exact e_eq_one (by ring) | exact e_eq_neg_one (by ring)

/-! ### Hadamard conjugation -/

/-- `H_t ; D ; H_t`, where `D` is the sign `-1` exactly when `f x` holds and bit `t` is
one, is the permutation matrix that flips bit `t` iff `f x`. -/
theorem h_sign_h (t : Fin N) (f : St N → Bool)
    (hf : ∀ x s, f (Function.update x t s) = f x) :
    oneMat t hGate * Matrix.diagonal (fun x => if f x && x t then (-1 : ℂ) else 1)
        * oneMat t hGate
      = mono (flipPerm t f hf) (fun _ => (1 : ℂ)) := by
  have hD : Matrix.diagonal (fun x : St N => if f x && x t then (-1 : ℂ) else 1)
      = ctrlMat t (fun x => Matrix.diagonal (fun s => if f x && s then (-1 : ℂ) else 1)) := by
    rw [ctrlMat_diagonal, mono_one_eq_diagonal]
  have h1 := ctrlMat_mul t (fun _ : St N => hGate)
    (fun x : St N => Matrix.diagonal (fun s => if f x && s then (-1 : ℂ) else 1))
    (fun _ _ => rfl)
  have h2 := ctrlMat_mul t
    (fun x : St N => hGate * Matrix.diagonal (fun s => if f x && s then (-1 : ℂ) else 1))
    (fun _ => hGate) (fun x s => by simp only [hf])
  rw [oneMat_eq_ctrlMat, hD, h1, h2, flip_eq_ctrlMat t f hf]
  congr 1
  funext x
  exact hGate_diag_hGate (f x)

/-! ### The exact Toffoli -/

/-- The gates of `toffoliExact N 0 1 2`. -/
theorem toffoliExact_eq (h : 2 < N) :
    toffoliExact N 0 1 2
      = Gate.one ⟨0, by omega⟩ hGate
        :: (signCirc ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, h⟩ (Or.inl rfl) (Or.inl rfl)
          ++ [Gate.one ⟨0, by omega⟩ hGate]) := by
  have h0 : 0 < N := by omega
  have h1 : 1 < N := by omega
  simp only [toffoliExact, show min 0 (min 1 2) = 0 from rfl, zero_add, uAt_eq 0 h0,
    uAt_eq 1 h1, uAt_eq 2 h, cxAt_eq 0 1 h0 h1 (Or.inl rfl), cxAt_eq 1 2 h1 h (Or.inl rfl)]
  rfl

/-- "Bits `1` and `2` are both one" does not depend on bit `0`. -/
theorem both_update (h : 2 < N) (x : St N) (s : Bool) :
    (Function.update x (⟨0, by omega⟩ : Fin N) s ⟨1, by omega⟩
        && Function.update x (⟨0, by omega⟩ : Fin N) s ⟨2, h⟩)
      = (x ⟨1, by omega⟩ && x ⟨2, h⟩) := by
  rw [Function.update_of_ne (fin_ne (by omega) (by omega) (by omega)),
    Function.update_of_ne (fin_ne (by omega) (by omega) (by omega))]

/-- **The exact Toffoli.**  The matrix of `toffoliExact N 0 1 2` is the permutation matrix
that flips bit `0` iff bits `1` and `2` are both one. -/
theorem circMat_toffoliExact (h : 2 < N) :
    circMat (toffoliExact N 0 1 2)
      = mono (flipPerm (⟨0, by omega⟩ : Fin N) (fun x => x ⟨1, by omega⟩ && x ⟨2, h⟩)
          (both_update h)) (fun _ => (1 : ℂ)) := by
  rw [toffoliExact_eq h, ← h_sign_h (⟨0, by omega⟩ : Fin N) _ (both_update h),
    ← circMat_signCirc _ _ _ (Or.inl rfl) (Or.inl rfl) (fin_ne (by omega) h (by omega))]
  simp only [circMat, circMat_append, Gate.mat, Matrix.one_mul, Matrix.mul_assoc]

theorem cnots_toffoliExact (h : 2 < N) : cnots (toffoliExact N 0 1 2) = 8 := by
  rw [toffoliExact_eq h]
  rfl

theorem unitaryGates_toffoliExact (h : 2 < N) : UnitaryGates (toffoliExact N 0 1 2) := by
  rw [toffoliExact_eq h]
  exact unitaryGates_cons_one _ hGate_unitary (unitaryGates_append
    (unitaryGates_signCirc _ _ _ _ _) (unitaryGates_cons_one _ hGate_unitary unitaryGates_nil))

end Helper
