/-
The fixed cells of Cirq's circuit: the one-qubit gates, the sign `ccz` (cell 1 of the
reference), the Toffoli `ccx` (cell 2) and the controlled root of X `croot` (cell 8).

For each cell: what its matrix is, how many CNOTs it has, and that its one-qubit gates
are unitary.
-/
import Mathlib
import ApproxToffoli.Free.CirqDefs
import ApproxToffoli.Free.ValeMcrz
import ApproxToffoli.Free.DspPass

namespace CirqMcx

open Matrix Free ExactLine
open Line (St hGate pGate xGate ryGate condMat cxFun cxPerm oneMat ctrlMat m2)
open Qulin (qb cx marg fmono pc)

variable {N : ℕ}

/-! ### One-qubit gates -/

theorem unitaryGates_hG (q : Fin N) : UnitaryGates (hG q) :=
  unitaryGates_singleton_one q Line.hGate_unitary

theorem unitaryGates_pG (φ : ℝ) (q : Fin N) : UnitaryGates (pG φ q) :=
  unitaryGates_singleton_one q (Line.pGate_unitary φ)

theorem cnots_hG (q : Fin N) : cnots (hG q) = 0 := rfl

theorem cnots_pG (φ : ℝ) (q : Fin N) : cnots (pG φ q) = 0 := rfl

theorem circMat_hG (q : Fin N) : circMat (hG q) = ctrlMat q (fun _ => hGate) := by
  rw [hG, circMat_singleton]
  rfl

theorem fmono_id (d : St N → ℂ) : fmono id d = Matrix.diagonal d := by
  ext y x
  by_cases h : y = x
  · subst h
    simp [fmono]
  · simp [fmono, h]

/-- A phase gate is the identity on basis states with the phase `e φ` where bit `q` is
one. -/
theorem circMat_pG (φ : ℝ) (q : Fin N) :
    circMat (pG φ q) = fmono id (fun x => e (if x q then φ else 0)) := by
  rw [fmono_id]
  exact Vale.circMat_pG φ q

theorem circMat_cx {c t : Fin N} (h : c ≠ t) :
    circMat (cx c t) = fmono (cxFun c t) (fun _ => 1) :=
  Qulin.acts_cx h

/-! ### Cell 1. The sign `ccz` -/

theorem cxFun_self (c t : Fin N) (x : St N) : cxFun c t x t = xor (x t) (x c) := by
  simp [cxFun]

theorem cxFun_of_ne (c t : Fin N) {r : Fin N} (h : r ≠ t) (x : St N) : cxFun c t x r = x r := by
  simp [cxFun, Function.update_of_ne h]

/-- Two sweeps `CX(a,b) ; CX(b,c)` are `CX(a,c)`. -/
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

/-- The angles of the seven phase gates of `ccz` add up to `π` when all three bits are
one, and to `0` otherwise. -/
theorem ccz_angle (θ : ℝ) (a b c : Bool) :
    (if xor (xor c a) (xor b a) then -θ else 0)
      + ((if xor (xor c (xor b a)) (xor (xor b a) a) then -θ else 0)
      + ((if xor c (xor b a) then θ else 0) + ((if xor b a then -θ else 0)
      + ((if c then θ else 0) + ((if b then θ else 0) + if a then θ else 0)))))
      = if a && b && c then 4 * θ else 0 := by
  cases a <;> cases b <;> cases c <;> (simp; try ring)

/-- **Cell 1.**  `ccz` is the sign `-1` exactly when all three bits are one. -/
theorem circMat_ccz {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    circMat (ccz a b c)
      = Matrix.diagonal (fun x => if x a && x b && x c then (-1 : ℂ) else 1) := by
  rw [← fmono_id]
  unfold ccz
  simp only [circMat_append, circMat_pG, circMat_cx hab, circMat_cx hbc, Qulin.fmono_mul]
  apply Qulin.fmono_congr
  · intro x
    simp only [Function.comp_apply, id]
    rw [sweep_sweep hab hac hbc, sweep_sweep hab hac hbc]
    exact Line.cxFun_involutive a c hac x
  · intro x
    simp only [Function.comp_apply, id, one_mul, ← e_add]
    simp only [sweep_sweep hab hac hbc, cxFun_self, cxFun_of_ne _ _ hbc.symm,
      cxFun_of_ne _ _ hbc, cxFun_of_ne _ _ hac, cxFun_of_ne _ _ hab]
    rw [ccz_angle]
    cases x a && x b && x c
    · simp [e_zero]
    · simp only [↓reduceIte]
      rw [show 4 * (Real.pi / 4) = Real.pi by ring, e_pi]

theorem cnots_ccz {a b c : Fin N} (hab : a ≠ b) (hbc : b ≠ c) : cnots (ccz a b c) = 8 := by
  unfold ccz
  simp only [cnots_append, Qulin.cnots_cx hab, Qulin.cnots_cx hbc, cnots_pG]

theorem unitaryGates_ccz (a b c : Fin N) : UnitaryGates (ccz a b c) := by
  unfold ccz
  simp only [unitaryGates_append_iff, unitaryGates_pG, Qulin.unitaryGates_cx, and_self]

/-! ### Cell 2. The Toffoli -/

/-- `H_t ; D ; H_t`, where `D` is the sign `-1` exactly when `f x` holds and bit `t` is
one, flips `t` iff `f x`. -/
theorem acts_h_sign_h (t : Fin N) (f : St N → Bool)
    (hf : ∀ x s, f (Function.update x t s) = f x) (c : List (Gate N))
    (hc : circMat c = Matrix.diagonal (fun x => if f x && x t then (-1 : ℂ) else 1)) :
    Acts (hG t ++ c ++ hG t) (fun x => Function.update x t (xor (x t) (f x))) := by
  have hD : Matrix.diagonal (fun x : St N => if f x && x t then (-1 : ℂ) else 1)
      = ctrlMat t (fun x => Matrix.diagonal (fun s => if f x && s then (-1 : ℂ) else 1)) := by
    rw [Line.ctrlMat_diagonal, Line.mono_one_eq_diagonal]
  have h1 := Line.ctrlMat_mul t
    (fun x : St N => Matrix.diagonal (fun s => if f x && s then (-1 : ℂ) else 1))
    (fun _ => hGate) (fun x s => by simp only [hf])
  have h2 := Line.ctrlMat_mul t (fun _ : St N => hGate)
    (fun x : St N => Matrix.diagonal (fun s => if f x && s then (-1 : ℂ) else 1) * hGate)
    (fun _ _ => rfl)
  unfold Acts
  rw [circMat_append, circMat_append, circMat_hG, hc, hD, h1, h2]
  simp only [← Matrix.mul_assoc, Line.hGate_diag_hGate]
  rw [← Line.flip_eq_ctrlMat t f hf]
  rfl

/-- **Cell 2.**  `ccx` flips `t` iff `c0` and `c1` are both one, exactly (no phase), in
each of the three orders of the sweep. -/
theorem acts_ccx {c0 c1 t : Fin N} (h01 : c0 ≠ c1) (h0t : c0 ≠ t) (h1t : c1 ≠ t) :
    Acts (ccx c0 c1 t) (fun x => Function.update x t (xor (x t) (x c0 && x c1))) := by
  unfold ccx
  apply acts_h_sign_h t (fun x => x c0 && x c1)
    (fun x s => by simp only [Function.update_of_ne h0t, Function.update_of_ne h1t])
  split_ifs
  · rw [circMat_ccz h0t h01 h1t.symm]
    congr 1
    funext x
    cases x c0 <;> cases x c1 <;> cases x t <;> rfl
  · rw [circMat_ccz h01.symm h1t h0t]
    congr 1
    funext x
    cases x c0 <;> cases x c1 <;> cases x t <;> rfl
  · rw [circMat_ccz h01 h0t h1t]

theorem cnots_ccx {c0 c1 t : Fin N} (h01 : c0 ≠ c1) (h0t : c0 ≠ t) (h1t : c1 ≠ t) :
    cnots (ccx c0 c1 t) = 8 := by
  unfold ccx
  rw [cnots_append, cnots_append, cnots_hG]
  split_ifs
  · rw [cnots_ccz h0t h1t.symm]
  · rw [cnots_ccz h01.symm h0t]
  · rw [cnots_ccz h01 h1t]

theorem unitaryGates_ccx (c0 c1 t : Fin N) : UnitaryGates (ccx c0 c1 t) := by
  unfold ccx
  refine unitaryGates_append (unitaryGates_append (unitaryGates_hG t) ?_) (unitaryGates_hG t)
  split_ifs <;> exact unitaryGates_ccz _ _ _

/-! ### Cell 8. The controlled root of X -/

theorem ryGate_mul (α β : ℝ) : ryGate α * ryGate β = ryGate (α + β) := by
  unfold Line.ryGate
  rw [Line.m2_mul, add_div, Real.cos_add, Real.sin_add]
  push_cast
  congr 1 <;> ring

theorem ryGate_zero : ryGate 0 = 1 := by
  unfold Line.ryGate
  rw [Line.one_eq_m2]
  simp

theorem x_ry_x (θ : ℝ) : xGate * ryGate θ * xGate = ryGate (-θ) := by
  unfold Line.ryGate
  rw [Line.xGate_eq_m2, Line.m2_mul, Line.m2_mul, neg_div, Real.cos_neg, Real.sin_neg]
  push_cast
  congr 1 <;> ring

theorem rzGate_mul (α β : ℝ) : rzGate α * rzGate β = rzGate (α + β) := by
  unfold rzGate
  rw [Line.m2_mul, add_div, neg_add, e_add, e_add]
  congr 1 <;> ring

theorem rzGate_zero : rzGate 0 = 1 := by
  unfold rzGate
  rw [Line.one_eq_m2]
  simp [e_zero]

theorem e_eq_cos_add_sin (t : ℝ) : e t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
  unfold ExactLine.e
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `R_x(φ)` in terms of the cosine and the sine. -/
theorem rx_eq (φ : ℝ) :
    Dsp.blk false φ
      = m2 (Real.cos (φ / 2) : ℂ) (-((Real.sin (φ / 2) : ℂ) * Complex.I))
          (-((Real.sin (φ / 2) : ℂ) * Complex.I)) (Real.cos (φ / 2) : ℂ) := by
  change Dsp.cyc (e (-(φ / 2))) (e (φ / 2)) = _
  unfold Dsp.cyc
  rw [e_eq_cos_add_sin, e_eq_cos_add_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  congr 1 <;> ring

theorem rz_ry_rz_pos (φ : ℝ) :
    rzGate (Real.pi / 2) * ryGate (-φ) * rzGate (-(Real.pi / 2)) = Dsp.blk false φ := by
  have h1 := Qulin.e_neg_mul_self (Real.pi / 4)
  have h2 := Vale.e_neg_quarter_sq
  have h3 := Line.e_quarter_sq
  rw [rx_eq]
  unfold rzGate Line.ryGate
  rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, show -(Real.pi / 2) / 2 = -(Real.pi / 4) by ring,
    neg_neg, neg_div, Real.cos_neg, Real.sin_neg, Line.m2_mul, Line.m2_mul]
  simp only [Complex.ofReal_neg, neg_neg]
  congr 1
  · linear_combination (Real.cos (φ / 2) : ℂ) * h1
  · linear_combination (Real.sin (φ / 2) : ℂ) * h2
  · linear_combination (-(Real.sin (φ / 2) : ℂ)) * h3
  · linear_combination (Real.cos (φ / 2) : ℂ) * h1

theorem rz_ry_rz_neg (φ : ℝ) :
    rzGate (-(Real.pi / 2)) * ryGate φ * rzGate (Real.pi / 2) = Dsp.blk false φ := by
  have h1 := Qulin.e_neg_mul_self (Real.pi / 4)
  have h2 := Vale.e_neg_quarter_sq
  have h3 := Line.e_quarter_sq
  rw [rx_eq]
  unfold rzGate Line.ryGate
  rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, show -(Real.pi / 2) / 2 = -(Real.pi / 4) by ring,
    neg_neg, Line.m2_mul, Line.m2_mul]
  congr 1
  · linear_combination (Real.cos (φ / 2) : ℂ) * h1
  · linear_combination (-(Real.sin (φ / 2) : ℂ)) * h3
  · linear_combination (Real.sin (φ / 2) : ℂ) * h2
  · linear_combination (Real.cos (φ / 2) : ℂ) * h1

/-- `R_x(φ)` times the phase `e^{iφ/2}` is `X^(φ/π)`. -/
theorem rx_mul_phase (φ : ℝ) :
    Dsp.blk false φ * Matrix.diagonal (fun _ : Bool => e (φ / 2)) = Dsp.blk true φ := by
  have h1 := Qulin.e_neg_mul_self (φ / 2)
  have h2 := Qulin.e_half_mul_half φ
  change Dsp.cyc (e (-(φ / 2))) (e (φ / 2)) * _ = Dsp.cyc 1 (e φ)
  unfold Dsp.cyc
  rw [Qulin.diagonal_const_eq_m2, Line.m2_mul]
  congr 1
  · linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2
  · linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2
  · linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2
  · linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2

/-- The 2×2 fact of cell 8: with the control off the six gates cancel, and with the
control on they are `X^s`. -/
theorem croot_block (s : ℝ) (u : Bool) :
    ((rzGate (sg s * (Real.pi / 2)) * ryGate (-(Real.pi * |s| / 2)) * if u then xGate else 1)
        * ryGate (Real.pi * |s| / 2) * if u then xGate else 1) * rzGate (-sg s * (Real.pi / 2))
        * Matrix.diagonal (fun _ : Bool => if u then e (Real.pi * s / 2) else 1)
      = if u then Dsp.blk true (Real.pi * s) else 1 := by
  cases u
  · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_one, Matrix.diagonal_one]
    rw [Matrix.mul_assoc (rzGate _), ryGate_mul, neg_add_cancel, ryGate_zero, Matrix.mul_one,
      rzGate_mul, show sg s * (Real.pi / 2) + -sg s * (Real.pi / 2) = 0 by ring, rzGate_zero]
  · simp only [↓reduceIte]
    have hre : rzGate (sg s * (Real.pi / 2)) * ryGate (-(Real.pi * |s| / 2)) * xGate
          * ryGate (Real.pi * |s| / 2) * xGate * rzGate (-sg s * (Real.pi / 2))
        = rzGate (sg s * (Real.pi / 2)) * ryGate (-(Real.pi * |s|))
          * rzGate (-sg s * (Real.pi / 2)) := by
      rw [Matrix.mul_assoc (rzGate _ * ryGate _), Matrix.mul_assoc (rzGate _ * ryGate _),
        x_ry_x, Matrix.mul_assoc (rzGate _), ryGate_mul]
      congr 3
      ring
    rw [hre, ← rx_mul_phase]
    congr 1
    by_cases hs : 0 < s
    · rw [sg, if_pos hs, abs_of_pos hs, one_mul, neg_one_mul]
      exact rz_ry_rz_pos _
    · rw [sg, if_neg hs, abs_of_nonpos (not_lt.1 hs), neg_neg, one_mul, neg_one_mul,
        mul_neg, neg_neg]
      exact rz_ry_rz_neg _

/-- **Cell 8.**  `croot s c t` is the block `X^s` on `t` when bit `c` is one. -/
theorem circMat_croot {c t : Fin N} (h : c ≠ t) (s : ℝ) :
    circMat (croot s c t)
      = ctrlMat t (fun x => if x c then Dsp.blk true (Real.pi * s) else 1) := by
  unfold croot pG
  rw [Qulin.cx_eq c t h]
  simp only [List.cons_append, List.nil_append, circMat, one_mul,
    Qulin.pGate_bot_mat_eq_ctrl2 c t c, Qulin.one_mat_eq_ctrl2 c t c,
    Qulin.cx_top_mat_eq_ctrl2 c t c, Line.ctrl2_mul c t c h h]
  unfold Line.ctrl2
  congr 1
  funext x
  exact croot_block s (x c)

theorem cnots_croot {c t : Fin N} (h : c ≠ t) (s : ℝ) : cnots (croot s c t) = 2 := by
  unfold croot pG
  rw [Qulin.cx_eq c t h]
  rfl

theorem rzGate_unitary (φ : ℝ) : rzGate φ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, rzGate, Line.star_m2, Line.m2_mul, Line.one_eq_m2]
  simp only [star_e, star_zero, neg_neg, mul_zero, zero_mul, add_zero, zero_add,
    Qulin.e_neg_mul_self, Qulin.e_mul_neg_self]

theorem unitaryGates_croot (s : ℝ) (c t : Fin N) : UnitaryGates (croot s c t) := by
  unfold croot
  have h1 : UnitaryGates [Gate.one t (rzGate (-sg s * (Real.pi / 2)))] :=
    unitaryGates_singleton_one t (rzGate_unitary _)
  have h2 : UnitaryGates [Gate.one t (ryGate (Real.pi * |s| / 2))] :=
    unitaryGates_singleton_one t (Line.ryGate_unitary _)
  have h3 : UnitaryGates
      [Gate.one t (rzGate (sg s * (Real.pi / 2)) * ryGate (-(Real.pi * |s| / 2)))] :=
    unitaryGates_singleton_one t (mul_mem (rzGate_unitary _) (Line.ryGate_unitary _))
  exact unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_append (unitaryGates_pG _ _) h1) (Qulin.unitaryGates_cx c t)) h2)
    (Qulin.unitaryGates_cx c t)) h3

end CirqMcx
