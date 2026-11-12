/-
The da Silva–Park circuit: the 2×2 blocks, the gate on one pair of qubits, and all
gates onto one target.

Every gate onto the target `t` is a block on qubit `t` chosen by the other bits
(`ctrlMat`), and the blocks form a one-parameter group (`blk_add`), so all gates onto
one target multiply to one block whose angle is the sum of the angles (`circMat_onto`).
-/
import Mathlib
import ApproxToffoli.Free.DspDefs
import ApproxToffoli.Free.QulinTop

namespace Dsp

open Matrix Free ExactLine
open Line (St hGate pGate xGate oneMat ctrlMat m2)
open Qulin (qb forUp)

variable {N : ℕ}

/-! ### The 2×2 blocks -/

/-- `H · diag(a, b) · H`. -/
noncomputable def cyc (a b : ℂ) : Matrix Bool Bool ℂ :=
  m2 ((a + b) / 2) ((a - b) / 2) ((a - b) / 2) ((a + b) / 2)

theorem hGate_diag (a b : ℂ) : hGate * m2 a 0 0 b * hGate = cyc a b := by
  rw [Line.hGate_mul_mul]
  unfold cyc
  congr 1 <;> ring

theorem cyc_mul (a b a' b' : ℂ) : cyc a b * cyc a' b' = cyc (a * a') (b * b') := by
  unfold cyc
  rw [Line.m2_mul]
  congr 1 <;> ring

theorem cyc_one : cyc 1 1 = 1 := by
  unfold cyc
  rw [Line.one_eq_m2]
  congr 1 <;> norm_num

/-- The block of angle `θ`: `X^(θ/π)` if `top`, and `R_x(θ)` otherwise. -/
noncomputable def blk (top : Bool) (θ : ℝ) : Matrix Bool Bool ℂ :=
  if top then cyc 1 (e θ) else cyc (e (-(θ / 2))) (e (θ / 2))

theorem blk_zero (top : Bool) : blk top 0 = 1 := by
  cases top <;> simp [blk, e_zero, cyc_one]

theorem blk_add (top : Bool) (θ θ' : ℝ) : blk top (θ + θ') = blk top θ * blk top θ' := by
  cases top
  · change cyc (e (-((θ + θ') / 2))) (e ((θ + θ') / 2))
      = cyc (e (-(θ / 2))) (e (θ / 2)) * cyc (e (-(θ' / 2))) (e (θ' / 2))
    rw [cyc_mul, ← e_add, ← e_add]
    congr 2 <;> ring
  · change cyc 1 (e (θ + θ')) = cyc 1 (e θ) * cyc 1 (e θ')
    rw [cyc_mul, one_mul, e_add]

theorem blk_add' (top : Bool) (θ θ' : ℝ) : blk top (θ + θ') = blk top θ' * blk top θ := by
  rw [add_comm, blk_add]

theorem ite_blk (top u : Bool) (θ : ℝ) :
    (if u then blk top θ else 1) = blk top (if u then θ else 0) := by
  cases u <;> simp [blk_zero]

theorem e_neg_pi : e (-Real.pi) = -1 := by
  rw [← star_e, e_pi]
  simp

theorem e_neg_pi_div_two : e (-(Real.pi / 2)) = -Complex.I := by
  rw [← star_e, Line.e_pi_div_two]
  simp

/-- The phase of the flip `blk top (± π)`: `1` for `X`, and `∓ i` for `R_x(± π)`. -/
noncomputable def kap (top neg : Bool) : ℂ :=
  if top then 1 else if neg then Complex.I else -Complex.I

/-- At the angle `± π` the block is a NOT up to the phase `kap`. -/
theorem blk_pi (top neg : Bool) :
    blk top ((if neg then -1 else 1) * Real.pi) = m2 0 (kap top neg) (kap top neg) 0 := by
  have h4 : -Real.pi / 2 = -(Real.pi / 2) := by ring
  cases top <;> cases neg <;>
    simp only [blk, kap, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, h4, neg_neg,
      e_neg_pi_div_two, Line.e_pi_div_two, e_pi, e_neg_pi] <;>
    unfold cyc <;> congr 1 <;> ring

/-! ### The gate on one pair of qubits -/

theorem crx_mid (θ : ℝ) (u : Bool) :
    (if u then xGate else 1) * pGate (-(θ / 2)) * (if u then xGate else 1) * pGate (θ / 2)
      = if u then m2 (e (-(θ / 2))) 0 0 (e (θ / 2)) else m2 1 0 0 1 := by
  cases u <;>
    simp only [↓reduceIte, Bool.false_eq_true, Line.pGate_eq_m2, Line.xGate_eq_m2,
      Line.one_eq_m2, Line.m2_mul, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      Qulin.e_neg_mul_self]

theorem crx_block (θ : ℝ) (u : Bool) :
    hGate * (if u then xGate else 1) * pGate (-(θ / 2)) * (if u then xGate else 1)
        * pGate (θ / 2) * hGate
      = if u then blk false θ else 1 := by
  have hre : hGate * (if u then xGate else 1) * pGate (-(θ / 2)) * (if u then xGate else 1)
        * pGate (θ / 2) * hGate
      = hGate * ((if u then xGate else 1) * pGate (-(θ / 2)) * (if u then xGate else 1)
        * pGate (θ / 2)) * hGate := by
    simp only [Matrix.mul_assoc]
  rw [hre, crx_mid]
  cases u
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hGate_diag, cyc_one]
  · simp only [↓reduceIte]
    rw [hGate_diag]
    rfl

theorem cxpow_block (θ : ℝ) (u : Bool) :
    hGate * Matrix.diagonal (fun b : Bool => if u = true ∧ b = true then e θ else 1) * hGate
      = if u then blk true θ else 1 := by
  cases u
  · have h : Matrix.diagonal (fun b : Bool => if false = true ∧ b = true then e θ else (1 : ℂ))
        = m2 1 0 0 1 := by
      ext i j
      cases i <;> cases j <;> simp [m2]
    rw [h, hGate_diag, cyc_one]
    rfl
  · have h : Matrix.diagonal (fun b : Bool => if true = true ∧ b = true then e θ else (1 : ℂ))
        = m2 1 0 0 (e θ) := by
      ext i j
      cases i <;> cases j <;> simp [m2]
    rw [h, hGate_diag]
    rfl

/-- Controlled `R_x(θ)`: the block `R_x(θ)` on `t` when bit `c` is one. -/
theorem circMat_crx {c t : Fin N} (h : c ≠ t) (θ : ℝ) :
    circMat (crx θ c t) = ctrlMat t (fun x => if x c then blk false θ else 1) := by
  unfold crx
  rw [Qulin.cx_eq c t h]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, Qulin.one_mat_eq_ctrl2 c t c,
    Qulin.cx_top_mat_eq_ctrl2 c t c, Line.ctrl2_mul c t c h h]
  unfold Line.ctrl2
  congr 1
  funext x
  exact crx_block θ (x c)

/-- Controlled `X^a`: the block `X^a` on `t` when bit `c` is one. -/
theorem circMat_cxpow {c t : Fin N} (h : c ≠ t) (a : ℝ) :
    circMat (cxpow a c t) = ctrlMat t (fun x => if x c then blk true (Real.pi * a) else 1) := by
  unfold cxpow
  rw [circMat_append, circMat_append, Qulin.circMat_cphase h, circMat_singleton]
  have hd : Matrix.diagonal
        (fun x : St N => if x c = true ∧ x t = true then e (Real.pi * a) else 1)
      = ctrlMat t (fun x => Matrix.diagonal
          (fun b => if x c = true ∧ b = true then e (Real.pi * a) else 1)) := by
    rw [Line.ctrlMat_diagonal, Line.mono_one_eq_diagonal]
  rw [hd]
  change ctrlMat t (fun _ => hGate) * (ctrlMat t _ * ctrlMat t (fun _ => hGate)) = _
  rw [Line.ctrlMat_mul t _ _ (fun x b => by rw [Function.update_of_ne h]),
    Line.ctrlMat_mul t _ _ (fun _ _ => rfl)]
  congr 1
  funext x
  rw [← Matrix.mul_assoc]
  exact cxpow_block _ (x c)

theorem cnots_crx {c t : Fin N} (h : c ≠ t) (θ : ℝ) : cnots (crx θ c t) = 2 := by
  unfold crx
  rw [Qulin.cx_eq c t h]
  rfl

theorem cnots_cxpow {c t : Fin N} (h : c ≠ t) (a : ℝ) : cnots (cxpow a c t) = 2 := by
  unfold cxpow
  simp only [cnots_append, Qulin.cnots_cphase h, cnots]

theorem unitaryGates_crx (θ : ℝ) (c t : Fin N) : UnitaryGates (crx θ c t) := by
  unfold crx
  have hp : ∀ φ : ℝ, UnitaryGates [Gate.one t (pGate φ)] :=
    fun φ => unitaryGates_singleton_one t (Line.pGate_unitary φ)
  have hh : UnitaryGates [Gate.one t hGate] := unitaryGates_singleton_one t Line.hGate_unitary
  exact unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_cons_one t Line.hGate_unitary (hp _)) (Qulin.unitaryGates_cx c t)) (hp _))
    (Qulin.unitaryGates_cx c t)) hh

theorem unitaryGates_cxpow (a : ℝ) (c t : Fin N) : UnitaryGates (cxpow a c t) := by
  unfold cxpow
  have hh : UnitaryGates [Gate.one t hGate] := unitaryGates_singleton_one t Line.hGate_unitary
  exact unitaryGates_append (unitaryGates_append hh (Qulin.unitaryGates_cphase _ c t)) hh

/-- **One pair gate**: on the target `t`, the block of angle `s π / 2^e` when the
control bit is one. -/
theorem circMat_pairGate (hN : 0 < N) (top : Bool) (s : ℝ) {c t : ℕ}
    (h : qb N hN c ≠ qb N hN t) :
    circMat (pairGate N hN top s c t)
      = ctrlMat (qb N hN t) (fun x => if x (qb N hN c)
          then blk (top && decide (t = N - 1)) (s * Real.pi / 2 ^ expo c t) else 1) := by
  unfold pairGate
  by_cases hc : top = true ∧ t = N - 1
  · have hb : (top && decide (t = N - 1)) = true := by simp [hc.1, hc.2]
    rw [if_pos hc, circMat_cxpow h, hb,
      show Real.pi * (s / 2 ^ expo c t) = s * Real.pi / 2 ^ expo c t by ring]
  · have hb : (top && decide (t = N - 1)) = false := by
      cases top <;> simp_all
    rw [if_neg hc, circMat_crx h, hb]

theorem cnots_pairGate (hN : 0 < N) (top : Bool) (s : ℝ) {c t : ℕ}
    (h : qb N hN c ≠ qb N hN t) : cnots (pairGate N hN top s c t) = 2 := by
  unfold pairGate
  split_ifs
  · exact cnots_cxpow h _
  · exact cnots_crx h _

theorem unitaryGates_pairGate (hN : 0 < N) (top : Bool) (s : ℝ) (c t : ℕ) :
    UnitaryGates (pairGate N hN top s c t) := by
  unfold pairGate
  split_ifs
  · exact unitaryGates_cxpow _ _ _
  · exact unitaryGates_crx _ _ _

/-! ### All gates onto one target -/

/-- The total angle on the target `t` from the controls `lo, ..., lo + m - 1`: the sum
of `sgn c · π / 2^(expo c t)` over the controls `c` whose bit is one. -/
noncomputable def ang (N : ℕ) (hN : 0 < N) (sgn : ℕ → ℝ) (lo t m : ℕ) (x : St N) : ℝ :=
  ∑ i ∈ Finset.range m,
    if x (qb N hN (lo + i)) then sgn (lo + i) * Real.pi / 2 ^ expo (lo + i) t else 0

theorem ang_zero (hN : 0 < N) (sgn : ℕ → ℝ) (lo t : ℕ) (x : St N) :
    ang N hN sgn lo t 0 x = 0 := rfl

theorem ang_succ (hN : 0 < N) (sgn : ℕ → ℝ) (lo t m : ℕ) (x : St N) :
    ang N hN sgn lo t (m + 1) x = ang N hN sgn lo t m x
      + (if x (qb N hN (lo + m)) then sgn (lo + m) * Real.pi / 2 ^ expo (lo + m) t else 0) :=
  Finset.sum_range_succ _ _

/-- The angle does not depend on the bits it does not read. -/
theorem ang_update (hN : 0 < N) (sgn : ℕ → ℝ) {lo t m r : ℕ} (hr : r < N) (hm : lo + m ≤ r)
    (x : St N) (b : Bool) :
    ang N hN sgn lo t m (Function.update x (qb N hN r) b) = ang N hN sgn lo t m x := by
  unfold ang
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.1 hi
  rw [Function.update_of_ne (Qulin.qb_ne hN (by omega) hr (by omega))]

theorem circMat_forUp_pair (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) {lo t : ℕ} (ht : t < N)
    (m : ℕ) (hm : lo + m ≤ t) :
    circMat (forUp m (fun i => pairGate N hN top (sgn (lo + i)) (lo + i) t))
      = ctrlMat (qb N hN t)
          (fun x => blk (top && decide (t = N - 1)) (ang N hN sgn lo t m x)) := by
  induction m with
  | zero =>
    rw [Qulin.forUp_zero]
    have h1 : (fun x : St N => blk (top && decide (t = N - 1)) (ang N hN sgn lo t 0 x))
        = fun _ => 1 := by
      funext x
      rw [ang_zero, blk_zero]
    rw [h1]
    exact (Line.oneMat_one (qb N hN t)).symm
  | succ m ih =>
    have hne : qb N hN (lo + m) ≠ qb N hN t := Qulin.qb_ne hN (by omega) ht (by omega)
    rw [Qulin.forUp_succ, circMat_append, ih (by omega), circMat_pairGate hN top _ hne,
      Line.ctrlMat_mul _ _ _ (fun x b => by rw [Function.update_of_ne hne])]
    congr 1
    funext x
    rw [ang_succ, blk_add', ite_blk]

/-- **All gates onto one target** multiply to one block on the target, whose angle is
the sum of the angles of the controls that are one. -/
theorem circMat_onto (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) {lo t : ℕ} (ht : t < N)
    (hlo : lo ≤ t) :
    circMat (onto N hN top sgn lo t)
      = ctrlMat (qb N hN t)
          (fun x => blk (top && decide (t = N - 1)) (ang N hN sgn lo t (t - lo) x)) :=
  circMat_forUp_pair hN top sgn ht (t - lo) (by omega)

theorem cnots_onto (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) {lo t : ℕ} (ht : t < N) :
    cnots (onto N hN top sgn lo t) = (t - lo) * 2 :=
  Qulin.cnots_forUp _ _ 2
    (fun i hi => cnots_pairGate hN top _ (Qulin.qb_ne hN (by omega) ht (by omega)))

theorem unitaryGates_onto (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) (lo t : ℕ) :
    UnitaryGates (onto N hN top sgn lo t) :=
  Qulin.unitaryGates_forUp _ _ (fun _ _ => unitaryGates_pairGate hN top _ _ _)

end Dsp

