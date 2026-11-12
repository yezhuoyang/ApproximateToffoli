/-
The fixed cells of the circuit of Vale et al.: the one-qubit gates, the calculus of
diagonal 2×2 blocks, the controlled `R_z` (S8), the three-controlled X without helper
qubit (S2), and the blocks of the ladder (S3, S4).

For each cell: what its matrix is, how many CNOTs it has, and that its one-qubit gates
are unitary.
-/
import Mathlib
import ApproxToffoli.Free.ValeDefs
import ApproxToffoli.Free.QulinMcx
import ApproxToffoli.Free.DspCells
import ApproxToffoli.Line.SignConj

namespace Vale

open Matrix Free ExactLine
open Line (St hGate pGate xGate condMat cxFun cxPerm oneMat ctrlMat m2)
open Qulin (qb cx ccx fmono)

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

theorem circMat_pG_ctrl (φ : ℝ) (q : Fin N) :
    circMat (pG φ q) = ctrlMat q (fun _ => pGate φ) := by
  rw [pG, circMat_singleton]
  rfl

/-- A phase gate is the diagonal matrix with entry `e φ` where bit `q` is one. -/
theorem circMat_pG (φ : ℝ) (q : Fin N) :
    circMat (pG φ q) = Matrix.diagonal (fun x => e (if x q then φ else 0)) := by
  rw [pG, circMat_singleton]
  change oneMat q (pGate φ) = _
  rw [Qulin.oneMat_pGate_eq_diagonal]
  congr 1
  funext x
  cases x q <;> simp [e_zero]

/-- The product of two diagonal matrices of phases: the angles add. -/
theorem diag_e_mul (f g : St N → ℝ) :
    Matrix.diagonal (fun x => e (f x)) * Matrix.diagonal (fun x => e (g x))
      = Matrix.diagonal (fun x => e (f x + g x)) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  rw [e_add]

/-! ### Diagonal 2×2 blocks -/

/-- The diagonal block `diag(e^{iα}, e^{iβ})`. -/
noncomputable def dg (α β : ℝ) : Matrix Bool Bool ℂ := m2 (e α) 0 0 (e β)

theorem pGate_eq_dg (θ : ℝ) : pGate θ = dg 0 θ := by
  rw [Line.pGate_eq_m2, dg, e_zero]

theorem dg_zero : dg 0 0 = 1 := by
  rw [dg, e_zero, Line.one_eq_m2]

theorem dg_mul (α β α' β' : ℝ) : dg α β * dg α' β' = dg (α + α') (β + β') := by
  unfold dg
  rw [Line.m2_mul, e_add, e_add]
  congr 1 <;> ring

theorem dg_mul_assoc (α β α' β' : ℝ) (M : Matrix Bool Bool ℂ) :
    dg α β * (dg α' β' * M) = dg (α + α') (β + β') * M := by
  rw [← Matrix.mul_assoc, dg_mul]

theorem x_mul_dg (α β : ℝ) : xGate * dg α β = dg β α * xGate := by
  unfold dg
  rw [Line.xGate_eq_m2, Line.m2_mul, Line.m2_mul]
  congr 1 <;> ring

theorem x_mul_dg_assoc (α β : ℝ) (M : Matrix Bool Bool ℂ) :
    xGate * (dg α β * M) = dg β α * (xGate * M) := by
  rw [← Matrix.mul_assoc, x_mul_dg, Matrix.mul_assoc]

theorem x_mul_x : xGate * xGate = 1 := by
  rw [Line.xGate_eq_m2, Line.m2_mul, Line.one_eq_m2]
  congr 1 <;> ring

theorem x_mul_x_assoc (M : Matrix Bool Bool ℂ) : xGate * (xGate * M) = M := by
  rw [← Matrix.mul_assoc, x_mul_x, Matrix.one_mul]

/-- A block `diag(e^{iα}, e^{iβ})` on qubit `t`, with angles chosen by the other bits,
is a diagonal matrix. -/
theorem ctrlMat_dg (t : Fin N) (α β : St N → ℝ) :
    ctrlMat t (fun x => dg (α x) (β x))
      = Matrix.diagonal (fun x => e (if x t then β x else α x)) := by
  have h : (fun x : St N => dg (α x) (β x))
      = fun x => Matrix.diagonal (fun s : Bool => e (if s then β x else α x)) := by
    funext x
    rw [Line.diagonal_eq_m2]
    rfl
  rw [h, Line.ctrlMat_diagonal, Line.mono_one_eq_diagonal]

/-! ### S8. The controlled `R_z` -/

theorem crz_block (lam : ℝ) (u : Bool) :
    (if u then xGate else 1) * pGate (-(lam / 2)) * (if u then xGate else 1) * pGate (lam / 2)
      = dg (if u then -(lam / 2) else 0) (if u then lam / 2 else 0) := by
  cases u <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one,
      pGate_eq_dg, x_mul_dg, x_mul_x, dg_mul] <;>
    congr 1 <;> ring

/-- **S8.**  `crz lam c t` is the diagonal matrix with entry `e^{± i lam / 2}` (sign `+`
if bit `t` is one) where bit `c` is one, and `1` elsewhere. -/
theorem circMat_crz {c t : Fin N} (h : c ≠ t) (lam : ℝ) :
    circMat (crz lam c t)
      = Matrix.diagonal
          (fun x => e (if x c then (if x t then lam / 2 else -(lam / 2)) else 0)) := by
  have h1 : circMat (crz lam c t)
      = ctrlMat t (fun x => dg (if x c then -(lam / 2) else 0) (if x c then lam / 2 else 0)) := by
    unfold crz pG
    rw [Qulin.cx_eq c t h]
    simp only [List.cons_append, List.nil_append, circMat, one_mul, Qulin.one_mat_eq_ctrl2 c t c,
      Qulin.cx_top_mat_eq_ctrl2 c t c, Line.ctrl2_mul c t c h h]
    unfold Line.ctrl2
    congr 1
    funext x
    exact crz_block lam (x c)
  rw [h1, ctrlMat_dg]
  congr 1
  funext x
  cases x c <;> cases x t <;> rfl

theorem cnots_crz {c t : Fin N} (h : c ≠ t) (lam : ℝ) : cnots (crz lam c t) = 2 := by
  unfold crz
  simp only [cnots_append, Qulin.cnots_cx h, cnots_pG]

theorem unitaryGates_crz (lam : ℝ) (c t : Fin N) : UnitaryGates (crz lam c t) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_pG _ _)
    (Qulin.unitaryGates_cx c t)) (unitaryGates_pG _ _)) (Qulin.unitaryGates_cx c t)

/-! ### S2. The three-controlled X without helper qubit -/

/-- The four phase gates at the start of `c3xCore`. -/
noncomputable def c3A (a b c t : Fin N) : List (Gate N) :=
  pG (Real.pi / 8) a ++ pG (Real.pi / 8) b ++ pG (Real.pi / 8) c ++ pG (Real.pi / 8) t

/-- The gates of `c3xCore` onto `b`. -/
noncomputable def c3B (a b : Fin N) : List (Gate N) :=
  cx a b ++ pG (-(Real.pi / 8)) b ++ cx a b

/-- The gates of `c3xCore` onto `c`. -/
noncomputable def c3C (a b c : Fin N) : List (Gate N) :=
  cx b c ++ pG (-(Real.pi / 8)) c ++ cx a c ++ pG (Real.pi / 8) c ++ cx b c ++
  pG (-(Real.pi / 8)) c ++ cx a c

/-- The gates of `c3xCore` onto `t`. -/
noncomputable def c3D (a b c t : Fin N) : List (Gate N) :=
  cx c t ++ pG (-(Real.pi / 8)) t ++ cx b t ++ pG (Real.pi / 8) t ++ cx c t ++
  pG (-(Real.pi / 8)) t ++
  cx a t ++ pG (Real.pi / 8) t ++ cx c t ++ pG (-(Real.pi / 8)) t ++ cx b t ++
  pG (Real.pi / 8) t ++
  cx c t ++ pG (-(Real.pi / 8)) t ++ cx a t

theorem c3xCore_split (a b c t : Fin N) :
    c3xCore a b c t = c3A a b c t ++ c3B a b ++ c3C a b c ++ c3D a b c t := by
  simp only [c3xCore, c3A, c3B, c3C, c3D, List.append_assoc]

theorem c3B_block (θ : ℝ) (u : Bool) :
    (if u then xGate else 1) * pGate (-θ) * (if u then xGate else 1)
      = dg (if u then -θ else 0) (if u then 0 else -θ) := by
  cases u <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one,
      pGate_eq_dg, x_mul_dg_assoc, x_mul_x, Matrix.mul_one]

theorem c3C_block (θ : ℝ) (u v : Bool) :
    (if u then xGate else 1) * pGate (-θ) * (if v then xGate else 1) * pGate θ
        * (if u then xGate else 1) * pGate (-θ) * (if v then xGate else 1)
      = dg (if u && v then -(2 * θ) else 0) (if u && v then θ else -θ) := by
  cases u <;> cases v <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one,
      pGate_eq_dg, x_mul_dg, x_mul_x, dg_mul_assoc, dg_mul,
      Bool.and_self, Bool.and_true, Bool.and_false] <;>
    congr 1 <;> ring

theorem c3D_block (θ : ℝ) (u v w : Bool) :
    (if u then xGate else 1) * pGate (-θ) * (if w then xGate else 1) * pGate θ
        * (if v then xGate else 1) * pGate (-θ) * (if w then xGate else 1) * pGate θ
        * (if u then xGate else 1) * pGate (-θ) * (if w then xGate else 1) * pGate θ
        * (if v then xGate else 1) * pGate (-θ) * (if w then xGate else 1)
      = dg (if u && v && w then -(4 * θ) else 0) (if u && v && w then 3 * θ else -θ) := by
  cases u <;> cases v <;> cases w <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one,
      pGate_eq_dg, x_mul_dg, x_mul_x, dg_mul_assoc, dg_mul,
      Bool.and_self, Bool.and_true, Bool.and_false] <;>
    congr 1 <;> ring

/-- The block `G (x a) (x b) (x c)` applied to qubit `t`. -/
def ctrl3 (a b c t : Fin N) (G : Bool → Bool → Bool → Matrix Bool Bool ℂ) :
    Matrix (St N) (St N) ℂ :=
  ctrlMat t (fun x => G (x a) (x b) (x c))

theorem ctrl3_mul (a b c t : Fin N) (ha : a ≠ t) (hb : b ≠ t) (hc : c ≠ t)
    (G G' : Bool → Bool → Bool → Matrix Bool Bool ℂ) :
    ctrl3 a b c t G * ctrl3 a b c t G' = ctrl3 a b c t (fun u v w => G u v w * G' u v w) := by
  refine Line.ctrlMat_mul t _ _ (fun x s => ?_)
  change G (Function.update x t s a) (Function.update x t s b) (Function.update x t s c)
    = G (x a) (x b) (x c)
  rw [Function.update_of_ne ha, Function.update_of_ne hb, Function.update_of_ne hc]

theorem one_mat_eq_ctrl3 (a b c t : Fin N) (g : Matrix Bool Bool ℂ) :
    (Gate.one t g).mat = ctrl3 a b c t (fun _ _ _ => g) := rfl

theorem cx_a_mat_eq_ctrl3 (a b c t : Fin N) (h : a ≠ t) :
    (Gate.cx a t h).mat = ctrl3 a b c t (fun u _ _ => if u then xGate else 1) :=
  Line.cx_eq_ctrlMat a t h

theorem cx_b_mat_eq_ctrl3 (a b c t : Fin N) (h : b ≠ t) :
    (Gate.cx b t h).mat = ctrl3 a b c t (fun _ v _ => if v then xGate else 1) :=
  Line.cx_eq_ctrlMat b t h

theorem cx_c_mat_eq_ctrl3 (a b c t : Fin N) (h : c ≠ t) :
    (Gate.cx c t h).mat = ctrl3 a b c t (fun _ _ w => if w then xGate else 1) :=
  Line.cx_eq_ctrlMat c t h

theorem circMat_c3A (a b c t : Fin N) :
    circMat (c3A a b c t)
      = Matrix.diagonal (fun x => e ((if x t then Real.pi / 8 else 0)
          + ((if x c then Real.pi / 8 else 0) + ((if x b then Real.pi / 8 else 0)
          + (if x a then Real.pi / 8 else 0))))) := by
  unfold c3A
  simp only [circMat_append, circMat_pG, diag_e_mul]

theorem circMat_c3B {a b : Fin N} (hab : a ≠ b) :
    circMat (c3B a b)
      = Matrix.diagonal (fun x => e (if x b then (if x a then 0 else -(Real.pi / 8))
          else (if x a then -(Real.pi / 8) else 0))) := by
  unfold c3B pG
  rw [Qulin.cx_eq a b hab]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, Qulin.one_mat_eq_ctrl2 a b a,
    Qulin.cx_top_mat_eq_ctrl2 a b a, Line.ctrl2_mul a b a hab hab, c3B_block]
  exact ctrlMat_dg b _ _

theorem circMat_c3C {a b c : Fin N} (hac : a ≠ c) (hbc : b ≠ c) :
    circMat (c3C a b c)
      = Matrix.diagonal (fun x => e (if x c then (if x a && x b then Real.pi / 8
            else -(Real.pi / 8))
          else (if x a && x b then -(2 * (Real.pi / 8)) else 0))) := by
  unfold c3C pG
  rw [Qulin.cx_eq a c hac, Qulin.cx_eq b c hbc]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, Qulin.one_mat_eq_ctrl2 a c b,
    Qulin.cx_top_mat_eq_ctrl2 a c b, Qulin.cx_bot_mat_eq_ctrl2 a c b,
    Line.ctrl2_mul a c b hac hbc, c3C_block]
  exact ctrlMat_dg c _ _

theorem circMat_c3D {a b c t : Fin N} (hat : a ≠ t) (hbt : b ≠ t) (hct : c ≠ t) :
    circMat (c3D a b c t)
      = Matrix.diagonal (fun x => e (if x t then (if x a && x b && x c then 3 * (Real.pi / 8)
            else -(Real.pi / 8))
          else (if x a && x b && x c then -(4 * (Real.pi / 8)) else 0))) := by
  unfold c3D pG
  rw [Qulin.cx_eq a t hat, Qulin.cx_eq b t hbt, Qulin.cx_eq c t hct]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, one_mat_eq_ctrl3 a b c t,
    cx_a_mat_eq_ctrl3 a b c t, cx_b_mat_eq_ctrl3 a b c t, cx_c_mat_eq_ctrl3 a b c t,
    ctrl3_mul a b c t hat hbt hct, c3D_block]
  exact ctrlMat_dg t _ _

/-- The angles of the four parts of `c3xCore` add up to `π` when all four bits are one,
and to `0` otherwise. -/
theorem c3x_angle (θ : ℝ) (a b c t : Bool) :
    (if t then (if a && b && c then 3 * θ else -θ) else (if a && b && c then -(4 * θ) else 0))
      + ((if c then (if a && b then θ else -θ) else (if a && b then -(2 * θ) else 0))
      + ((if b then (if a then 0 else -θ) else (if a then -θ else 0))
      + ((if t then θ else 0) + ((if c then θ else 0) + ((if b then θ else 0)
      + (if a then θ else 0))))))
      = if a && b && c && t then 8 * θ else 0 := by
  cases a <;> cases b <;> cases c <;> cases t <;> simp <;> ring

/-- **The diagonal part of `c3x`**: the sign `-1` exactly when all four bits are one. -/
theorem circMat_c3xCore {a b c t : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hat : a ≠ t) (hbt : b ≠ t) (hct : c ≠ t) :
    circMat (c3xCore a b c t)
      = Matrix.diagonal (fun x => if (x a && x b && x c) && x t then (-1 : ℂ) else 1) := by
  rw [c3xCore_split]
  simp only [circMat_append, circMat_c3A, circMat_c3B hab, circMat_c3C hac hbc,
    circMat_c3D hat hbt hct, diag_e_mul]
  congr 1
  funext x
  rw [c3x_angle]
  cases x a && x b && x c && x t
  · simp [e_zero]
  · simp only [↓reduceIte]
    rw [show 8 * (Real.pi / 8) = Real.pi by ring, e_pi]

/-- **S2.**  `c3x` flips `t` iff `a`, `b`, `c` are all one, exactly (no phase). -/
theorem acts_c3x {a b c t : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hat : a ≠ t) (hbt : b ≠ t) (hct : c ≠ t) :
    Acts (c3x a b c t) (fun x => Function.update x t (xor (x t) (x a && x b && x c))) := by
  have hf : ∀ (x : St N) (s : Bool),
      (Function.update x t s a && Function.update x t s b && Function.update x t s c)
        = (x a && x b && x c) := by
    intro x s
    rw [Function.update_of_ne hat, Function.update_of_ne hbt, Function.update_of_ne hct]
  have hD : Matrix.diagonal (fun x : St N => if (x a && x b && x c) && x t then (-1 : ℂ) else 1)
      = ctrlMat t (fun x => Matrix.diagonal
          (fun s => if (x a && x b && x c) && s then (-1 : ℂ) else 1)) := by
    rw [Line.ctrlMat_diagonal, Line.mono_one_eq_diagonal]
  have h1 := Line.ctrlMat_mul t
    (fun x : St N => Matrix.diagonal (fun s => if (x a && x b && x c) && s then (-1 : ℂ) else 1))
    (fun _ => hGate) (fun x s => by simp only [hf])
  have h2 := Line.ctrlMat_mul t (fun _ : St N => hGate)
    (fun x : St N => Matrix.diagonal (fun s => if (x a && x b && x c) && s then (-1 : ℂ) else 1)
      * hGate) (fun _ _ => rfl)
  unfold Acts c3x
  rw [circMat_append, circMat_append, circMat_hG, circMat_c3xCore hab hac hbc hat hbt hct, hD,
    h1, h2]
  simp only [← Matrix.mul_assoc, Line.hGate_diag_hGate]
  rw [← Line.flip_eq_ctrlMat t (fun x => x a && x b && x c) hf]
  rfl

theorem cnots_c3x {a b c t : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hat : a ≠ t) (hbt : b ≠ t) (hct : c ≠ t) : cnots (c3x a b c t) = 14 := by
  unfold c3x c3xCore
  simp only [cnots_append, Qulin.cnots_cx hab, Qulin.cnots_cx hac, Qulin.cnots_cx hbc,
    Qulin.cnots_cx hat, Qulin.cnots_cx hbt, Qulin.cnots_cx hct, cnots_pG, cnots_hG]

theorem unitaryGates_c3x (a b c t : Fin N) : UnitaryGates (c3x a b c t) := by
  unfold c3x c3xCore
  simp only [unitaryGates_append_iff, unitaryGates_pG, unitaryGates_hG, Qulin.unitaryGates_cx,
    and_self]

end Vale
