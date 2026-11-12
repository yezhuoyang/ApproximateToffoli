/-
The small cells of the Huang–Palsberg circuit: CNOT, `forUp`, the Toffoli, the
controlled phases, and the counts of the relative-phase pieces.

For each cell: what its matrix is (as a function on basis states, `Acts`, or as a
diagonal matrix), how many CNOTs it has, its T accounting (`TR`), and that its
one-qubit gates are unitary.
-/
import Mathlib
import ApproxToffoli.Free.QulinDefs
import ApproxToffoli.Free.Acts
import ApproxToffoli.Line.Rccx
import ApproxToffoli.Line.Inverse
import ApproxToffoli.Line.TGates

namespace Qulin

open Matrix Free ExactLine
open Line (St hGate pGate xGate ryGate condMat cxFun cxPerm oneMat ctrlMat m2)

variable {N : ℕ}

/-! ### A. The CNOT and the NOT -/

theorem cx_eq (c t : Fin N) (h : c ≠ t) : cx c t = [Gate.cx c t h] := by
  unfold cx
  rw [dif_pos h]

theorem acts_cx {c t : Fin N} (h : c ≠ t) : Acts (cx c t) (cxFun c t) := by
  rw [cx_eq c t h]
  exact acts_cx_gate c t h

theorem circMat_cx {c t : Fin N} (h : c ≠ t) :
    circMat (cx c t) = mono (cxPerm c t h) (fun _ => 1) := by
  rw [cx_eq c t h, circMat_singleton]
  rfl

theorem cnots_cx {c t : Fin N} (h : c ≠ t) : cnots (cx c t) = 1 := by
  rw [cx_eq c t h]
  rfl

theorem tr_cx (c t : Fin N) : TR (cx c t) 0 0 := by
  unfold cx
  by_cases h : c ≠ t
  · rw [dif_pos h]
    exact TR.cx c t h TR.nil
  · rw [dif_neg h]
    exact TR.nil

theorem unitaryGates_cx (c t : Fin N) : UnitaryGates (cx c t) := by
  unfold cx
  by_cases h : c ≠ t
  · rw [dif_pos h]
    exact unitaryGates_singleton_cx c t h
  · rw [dif_neg h]
    exact unitaryGates_nil

theorem acts_x (q : Fin N) :
    Acts [Gate.one q xGate] (fun x => Function.update x q (!x q)) := by
  unfold Acts
  rw [circMat_singleton]
  ext y x
  have key : (y = Function.update x q (!x q)) ↔ (y q = !x q) ∧ ∀ r, r ≠ q → y r = x r :=
    Function.eq_update_iff
  change (if (∀ r, r ≠ q → y r = x r) then xGate (y q) (x q) else 0)
    = if y = Function.update x q (!x q) then 1 else 0
  by_cases h1 : ∀ r, r ≠ q → y r = x r
  · by_cases h2 : y q = !x q
    · rw [if_pos h1, if_pos (key.2 ⟨h2, h1⟩)]
      simp [xGate, h2]
    · rw [if_pos h1, if_neg (fun h => h2 (key.1 h).1)]
      simp [xGate, h2]
  · rw [if_neg h1, if_neg (fun h => h1 (key.1 h).2)]

/-! ### B. `forUp` -/

theorem forUp_zero (f : ℕ → List (Gate N)) : forUp 0 f = [] := rfl

theorem forUp_succ (m : ℕ) (f : ℕ → List (Gate N)) : forUp (m + 1) f = forUp m f ++ f m := by
  simp [forUp, List.range_succ]

theorem cnots_forUp (m : ℕ) (f : ℕ → List (Gate N)) (n : ℕ)
    (h : ∀ i < m, cnots (f i) = n) : cnots (forUp m f) = m * n := by
  induction m with
  | zero => simp [forUp_zero, cnots]
  | succ m ih =>
    rw [forUp_succ, cnots_append, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h m (Nat.lt_succ_self m), Nat.succ_mul]

theorem tr_forUp (m : ℕ) (f : ℕ → List (Gate N)) (t r : ℕ)
    (h : ∀ i < m, TR (f i) t r) : TR (forUp m f) (m * t) (m * r) := by
  induction m with
  | zero =>
    rw [forUp_zero, Nat.zero_mul, Nat.zero_mul]
    exact TR.nil
  | succ m ih =>
    rw [forUp_succ, Nat.succ_mul, Nat.succ_mul]
    exact tr_append (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h m (Nat.lt_succ_self m))

theorem unitaryGates_forUp (m : ℕ) (f : ℕ → List (Gate N))
    (h : ∀ i < m, UnitaryGates (f i)) : UnitaryGates (forUp m f) := by
  induction m with
  | zero =>
    rw [forUp_zero]
    exact unitaryGates_nil
  | succ m ih =>
    rw [forUp_succ]
    exact unitaryGates_append (ih (fun i hi => h i (Nat.lt_succ_of_lt hi)))
      (h m (Nat.lt_succ_self m))

/-! ### Diagonal matrices, phase gates and CNOTs -/

theorem oneMat_pGate_eq_diagonal (q : Fin N) (θ : ℝ) :
    oneMat q (pGate θ) = Matrix.diagonal (fun x => if x q = true then e θ else 1) := by
  rw [Line.oneMat_pGate, Line.mono_one_eq_diagonal]

/-- A diagonal matrix between two copies of the same CNOT is diagonal. -/
theorem cx_mul_diagonal_mul_cx (c t : Fin N) (h : c ≠ t) (d : St N → ℂ) :
    mono (cxPerm c t h) (fun _ => (1 : ℂ)) * Matrix.diagonal d
        * mono (cxPerm c t h) (fun _ => (1 : ℂ))
      = Matrix.diagonal (fun x => d (cxFun c t x)) := by
  have h1 := Line.conj_mono_diagonal (cxPerm c t h) (fun _ => (1 : ℂ)) d (fun _ => by simp)
  rw [Line.conjTranspose_cx] at h1
  exact h1

/-- A diagonal matrix after a permutation up to phases. -/
theorem diagonal_mul_mono (σ : Equiv.Perm (St N)) (d φ : St N → ℂ) :
    Matrix.diagonal d * mono σ φ = mono σ (fun x => d (σ x) * φ x) := by
  rw [← Line.mono_one_eq_diagonal, Line.mono_mul]
  rfl

theorem e_neg_mul_self (s : ℝ) : e (-s) * e s = 1 := by
  rw [← e_add, neg_add_cancel, e_zero]

theorem e_mul_neg_self (s : ℝ) : e s * e (-s) = 1 := by
  rw [← e_add, add_neg_cancel, e_zero]

theorem e_half_mul_half (s : ℝ) : e (s / 2) * e (s / 2) = e s := by
  rw [← e_add, add_halves]

/-! ### D. The controlled phase -/

theorem circMat_cphase {c t : Fin N} (h : c ≠ t) (θ : ℝ) :
    circMat (cphase θ c t)
      = Matrix.diagonal (fun x => if x c = true ∧ x t = true then e θ else 1) := by
  unfold cphase
  rw [cx_eq c t h]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, Gate.mat]
  rw [oneMat_pGate_eq_diagonal, oneMat_pGate_eq_diagonal, oneMat_pGate_eq_diagonal,
    cx_mul_diagonal_mul_cx, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  have h1 := e_neg_mul_self (θ / 2)
  have h2 := e_half_mul_half θ
  simp only [cxFun, Function.update_self]
  cases x c <;> cases x t <;> simp [h1, h2]

theorem cnots_cphase {c t : Fin N} (h : c ≠ t) (θ : ℝ) : cnots (cphase θ c t) = 2 := by
  unfold cphase
  rw [cx_eq c t h]
  rfl

theorem unitaryGates_cphase (θ : ℝ) (c t : Fin N) : UnitaryGates (cphase θ c t) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_cons_one c (Line.pGate_unitary _)
      (unitaryGates_singleton_one t (Line.pGate_unitary _)))
    (unitaryGates_cx c t)) (unitaryGates_singleton_one t (Line.pGate_unitary _)))
    (unitaryGates_cx c t)

/-- A single one-qubit gate of known T cost. -/
theorem tr_one (q : Fin N) {g : Matrix Bool Bool ℂ} {m : ℕ} (hg : Line.TCost g m) :
    TR [Gate.one q g] m 0 := by
  have h := TR.exact q hg (TR.nil (N := N))
  rwa [Nat.zero_add] at h

/-- A single phase gate, counted as a rotation. -/
theorem tr_rot_one (q : Fin N) (φ : ℝ) : TR [Gate.one q (pGate φ)] 0 1 :=
  TR.rot q φ TR.nil

theorem tr_cphase_rot (θ : ℝ) (c t : Fin N) : TR (cphase θ c t) 0 3 :=
  tr_append (tr_append (tr_append (TR.rot c _ (tr_rot_one t _)) (tr_cx c t))
    (tr_rot_one t _)) (tr_cx c t)

theorem tr_cphase_T (c t : Fin N) : TR (cphase (Real.pi / 2) c t) 3 0 := by
  unfold cphase
  rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring]
  exact tr_append (tr_append (tr_append
    (TR.exact c Line.tcost_pGate_quarter (tr_one t Line.tcost_pGate_quarter)) (tr_cx c t))
    (tr_one t Line.tcost_pGate_neg_quarter)) (tr_cx c t)

theorem tr_cphase_T_neg (c t : Fin N) : TR (cphase (-(Real.pi / 2)) c t) 3 0 := by
  unfold cphase
  rw [show -(Real.pi / 2) / 2 = -(Real.pi / 4) by ring, neg_neg]
  exact tr_append (tr_append (tr_append
    (TR.exact c Line.tcost_pGate_neg_quarter (tr_one t Line.tcost_pGate_neg_quarter))
    (tr_cx c t)) (tr_one t Line.tcost_pGate_quarter)) (tr_cx c t)

/-! ### Blocks on one qubit with two classical controls -/

theorem one_mat_eq_ctrl2 (top mid bot : Fin N) (g : Matrix Bool Bool ℂ) :
    (Gate.one mid g).mat = Line.ctrl2 top mid bot (fun _ _ => g) := rfl

theorem cx_top_mat_eq_ctrl2 (top mid bot : Fin N) (h : top ≠ mid) :
    (Gate.cx top mid h).mat = Line.ctrl2 top mid bot (fun u _ => if u then xGate else 1) :=
  Line.cx_eq_ctrlMat top mid h

theorem cx_bot_mat_eq_ctrl2 (top mid bot : Fin N) (h : bot ≠ mid) :
    (Gate.cx bot mid h).mat = Line.ctrl2 top mid bot (fun _ v => if v then xGate else 1) :=
  Line.cx_eq_ctrlMat bot mid h

/-- A phase gate on the control `bot`, seen as a (scalar) block on `mid`. -/
theorem pGate_bot_mat_eq_ctrl2 (top mid bot : Fin N) (θ : ℝ) :
    (Gate.one bot (pGate θ)).mat
      = Line.ctrl2 top mid bot (fun _ v => Matrix.diagonal (fun _ => if v then e θ else 1)) :=
  (Line.oneMat_pGate bot θ).trans
    (Line.ctrlMat_diagonal mid (fun x _ => if x bot then e θ else 1)).symm

theorem mul_e_mul_neg (z : ℂ) (s : ℝ) : z * e s * e (-s) = z := by
  rw [mul_assoc, e_mul_neg_self, mul_one]

theorem mul_e_neg_mul (z : ℂ) (s : ℝ) : z * e (-s) * e s = z := by
  rw [mul_assoc, e_neg_mul_self, mul_one]

theorem ccphase_block (s : ℝ) (u v : Bool) :
    pGate s * (if v then xGate else 1) * pGate (-s) * (if u then xGate else 1)
        * pGate s * (if v then xGate else 1) * pGate (-s) * (if u then xGate else 1)
      = Matrix.diagonal (fun b => if u && v then (if b then e s * e s else e (-s) * e (-s))
          else 1) := by
  cases u <;> cases v <;>
    simp only [↓reduceIte, Bool.false_eq_true, Line.pGate_eq_m2, Line.xGate_eq_m2,
      Line.one_eq_m2, Line.m2_mul, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      e_mul_neg_self, e_neg_mul_self, Bool.and_self, Bool.and_false, Bool.and_true]
  all_goals
    ext i j
    cases i <;> cases j <;> simp [m2]

/-- The eight gates of `ccphase` on the target: a phase on `t` when both controls are one. -/
theorem circMat_ccphase_head {c0 c1 t : Fin N} (h0 : c0 ≠ t) (h1 : c1 ≠ t) (s : ℝ) :
    circMat (cx c0 t ++ [Gate.one t (pGate (-s))] ++ cx c1 t ++ [Gate.one t (pGate s)] ++
        cx c0 t ++ [Gate.one t (pGate (-s))] ++ cx c1 t ++ [Gate.one t (pGate s)])
      = Matrix.diagonal (fun x => if x c0 && x c1 then
          (if x t then e s * e s else e (-s) * e (-s)) else 1) := by
  rw [cx_eq c0 t h0, cx_eq c1 t h1]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, one_mat_eq_ctrl2 c0 t c1,
    cx_top_mat_eq_ctrl2 c0 t c1, cx_bot_mat_eq_ctrl2 c0 t c1, Line.ctrl2_mul c0 t c1 h0 h1,
    ccphase_block]
  rw [← Line.mono_one_eq_diagonal]
  exact Line.ctrlMat_diagonal t
    (fun x b => if x c0 && x c1 then (if b then e s * e s else e (-s) * e (-s)) else 1)

theorem circMat_ccphase {c0 c1 t : Fin N} (h01 : c0 ≠ c1) (h0 : c0 ≠ t) (h1 : c1 ≠ t) (θ : ℝ) :
    circMat (ccphase θ c0 c1 t)
      = Matrix.diagonal
          (fun x => if x c0 = true ∧ x c1 = true ∧ x t = true then e θ else 1) := by
  unfold ccphase
  rw [circMat_append, circMat_ccphase_head h0 h1, circMat_cphase h01,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  have h2 : e (θ / 2) * (e (θ / 4) * e (θ / 4)) = e θ := by
    rw [← e_add, ← e_add]
    congr 1
    ring
  have h3 : e (θ / 2) * (e (-(θ / 4)) * e (-(θ / 4))) = 1 := by
    rw [← e_add, ← e_add, ← e_zero]
    congr 1
    ring
  cases x c0 <;> cases x c1 <;> cases x t <;> simp [h2, h3]

theorem cnots_ccphase {c0 c1 t : Fin N} (h01 : c0 ≠ c1) (h0 : c0 ≠ t) (h1 : c1 ≠ t) (θ : ℝ) :
    cnots (ccphase θ c0 c1 t) = 6 := by
  unfold ccphase
  simp only [cnots_append, cnots_cx h0, cnots_cx h1, cnots_cphase h01, cnots]

theorem unitaryGates_ccphase (θ : ℝ) (c0 c1 t : Fin N) : UnitaryGates (ccphase θ c0 c1 t) := by
  unfold ccphase
  simp only [unitaryGates_append_iff]
  have hp : ∀ φ : ℝ, UnitaryGates [Gate.one t (pGate φ)] :=
    fun φ => unitaryGates_singleton_one t (Line.pGate_unitary φ)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨unitaryGates_cx _ _, hp _⟩, unitaryGates_cx _ _⟩, hp _⟩, unitaryGates_cx _ _⟩,
    hp _⟩, unitaryGates_cx _ _⟩, hp _⟩, unitaryGates_cphase _ _ _⟩

theorem tr_ccphase_rot (θ : ℝ) (c0 c1 t : Fin N) : TR (ccphase θ c0 c1 t) 0 7 :=
  tr_append (tr_append (tr_append (tr_append (tr_append (tr_append (tr_append (tr_append
    (tr_cx c0 t) (tr_rot_one t _)) (tr_cx c1 t)) (tr_rot_one t _)) (tr_cx c0 t))
    (tr_rot_one t _)) (tr_cx c1 t)) (tr_rot_one t _)) (tr_cphase_rot _ c0 c1)

/-! ### C. The Toffoli -/

theorem diagonal_const_eq_m2 (c : ℂ) : Matrix.diagonal (fun _ : Bool => c) = m2 c 0 0 c := by
  ext i j
  cases i <;> cases j <;> simp [m2]

theorem ccx_mid (u v : Bool) :
    pGate (Real.pi / 4) * Matrix.diagonal (fun _ => if v then e (Real.pi / 4) else 1)
        * (if u then xGate else 1) * pGate (-(Real.pi / 4)) * (if v then xGate else 1)
        * pGate (Real.pi / 4) * (if u then xGate else 1) * pGate (-(Real.pi / 4))
        * (if v then xGate else 1)
      = if v then
          (if u then m2 (e (-(Real.pi / 4))) 0 0
              (e (Real.pi / 4) * e (Real.pi / 4) * e (Real.pi / 4))
            else m2 (e (Real.pi / 4)) 0 0 (e (Real.pi / 4)))
        else m2 1 0 0 1 := by
  cases u <;> cases v <;>
    simp only [↓reduceIte, Bool.false_eq_true, Line.pGate_eq_m2, Line.xGate_eq_m2,
      Line.one_eq_m2, Line.m2_mul, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      e_mul_neg_self, e_neg_mul_self, mul_e_mul_neg, diagonal_const_eq_m2]

theorem e_quarter_cube :
    e (Real.pi / 4) * e (Real.pi / 4) * e (Real.pi / 4) = -e (-(Real.pi / 4)) := by
  have hq := Line.e_quarter_sq
  have hc := e_neg_mul_self (Real.pi / 4)
  linear_combination (-(e (Real.pi / 4)) ^ 3) * hc
    + e (-(Real.pi / 4)) * (e (Real.pi / 4) ^ 2 + Complex.I) * hq
    + e (-(Real.pi / 4)) * Complex.I_mul_I

/-- The block of the first eleven gates of the Toffoli (those on the target, and the
`T` on the second control): `1, 1, e^{iπ/4}, e^{-iπ/4} X` for
`(u, v) = (0,0), (1,0), (0,1), (1,1)`. -/
noncomputable def ccxBlock (u v : Bool) : Matrix Bool Bool ℂ :=
  if v then
    (if u then m2 0 (e (-(Real.pi / 4))) (e (-(Real.pi / 4))) 0
      else m2 (e (Real.pi / 4)) 0 0 (e (Real.pi / 4)))
  else m2 1 0 0 1

theorem ccx_block (u v : Bool) :
    hGate * pGate (Real.pi / 4) * Matrix.diagonal (fun _ => if v then e (Real.pi / 4) else 1)
        * (if u then xGate else 1) * pGate (-(Real.pi / 4)) * (if v then xGate else 1)
        * pGate (Real.pi / 4) * (if u then xGate else 1) * pGate (-(Real.pi / 4))
        * (if v then xGate else 1) * hGate
      = ccxBlock u v := by
  have hre : hGate * pGate (Real.pi / 4)
        * Matrix.diagonal (fun _ => if v then e (Real.pi / 4) else 1)
        * (if u then xGate else 1) * pGate (-(Real.pi / 4)) * (if v then xGate else 1)
        * pGate (Real.pi / 4) * (if u then xGate else 1) * pGate (-(Real.pi / 4))
        * (if v then xGate else 1) * hGate
      = hGate * (pGate (Real.pi / 4)
        * Matrix.diagonal (fun _ => if v then e (Real.pi / 4) else 1)
        * (if u then xGate else 1) * pGate (-(Real.pi / 4)) * (if v then xGate else 1)
        * pGate (Real.pi / 4) * (if u then xGate else 1) * pGate (-(Real.pi / 4))
        * (if v then xGate else 1)) * hGate := by
    simp only [Matrix.mul_assoc]
  rw [hre, ccx_mid, e_quarter_cube]
  cases u <;> cases v <;>
    simp only [↓reduceIte, Bool.false_eq_true, Line.hGate_mul_mul, ccxBlock] <;>
    congr 1 <;> ring

/-- The first eleven gates of the Toffoli. -/
noncomputable def ccxHead (a b t : Fin N) : List (Gate N) :=
  [Gate.one t hGate] ++ cx b t ++ [Gate.one t (pGate (-(Real.pi / 4)))] ++ cx a t ++
  [Gate.one t (pGate (Real.pi / 4))] ++ cx b t ++ [Gate.one t (pGate (-(Real.pi / 4)))] ++
  cx a t ++
  [Gate.one b (pGate (Real.pi / 4)), Gate.one t (pGate (Real.pi / 4)), Gate.one t hGate]

/-- The last four gates of the Toffoli. -/
noncomputable def ccxTail (a b : Fin N) : List (Gate N) :=
  cx a b ++ [Gate.one a (pGate (Real.pi / 4)), Gate.one b (pGate (-(Real.pi / 4)))] ++ cx a b

theorem ccx_split (a b t : Fin N) : ccx a b t = ccxHead a b t ++ ccxTail a b := by
  simp only [ccx, ccxHead, ccxTail, List.append_assoc]

theorem circMat_ccxHead {a b t : Fin N} (hat : a ≠ t) (hbt : b ≠ t) :
    circMat (ccxHead a b t) = Line.ctrl2 a t b ccxBlock := by
  unfold ccxHead
  rw [cx_eq a t hat, cx_eq b t hbt]
  simp only [List.cons_append, List.nil_append, circMat, one_mul,
    pGate_bot_mat_eq_ctrl2 a t b, one_mat_eq_ctrl2 a t b,
    cx_top_mat_eq_ctrl2 a t b, cx_bot_mat_eq_ctrl2 a t b, Line.ctrl2_mul a t b hat hbt]
  congr 1
  funext u v
  exact ccx_block u v

/-- The phases left by the first eleven gates of the Toffoli. -/
noncomputable def ccxHeadPhase (a b : Fin N) (x : St N) : ℂ :=
  if x b then (if x a then e (-(Real.pi / 4)) else e (Real.pi / 4)) else 1

theorem ctrl2_ccxBlock {a b t : Fin N} (hat : a ≠ t) (hbt : b ≠ t) :
    Line.ctrl2 a t b ccxBlock = mono (Line.ccPerm a t b hat hbt) (ccxHeadPhase a b) := by
  have hg : ∀ (x : St N) (p q : Bool), p ≠ xor q (x a && x b) →
      ccxBlock (x a) (x b) p q = 0 := by
    intro x p q
    unfold ccxBlock
    cases x a <;> cases x b <;> cases p <;> cases q <;> simp [m2]
  rw [Line.ctrl2, Line.ccPerm, Line.ctrlMat_eq_mono t (fun x => x a && x b) _ _ hg]
  · congr 1
    funext x
    unfold ccxHeadPhase ccxBlock
    cases x b <;> cases x a <;> cases x t <;> simp [m2]
  · intro x p
    change (Function.update x t p a && Function.update x t p b) = (x a && x b)
    rw [Function.update_of_ne hat, Function.update_of_ne hbt]

theorem circMat_ccxTail {a b : Fin N} (hab : a ≠ b) :
    circMat (ccxTail a b)
      = Matrix.diagonal (fun x => (if xor (x b) (x a) then e (-(Real.pi / 4)) else 1)
          * (if x a then e (Real.pi / 4) else 1)) := by
  unfold ccxTail
  rw [cx_eq a b hab]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, Gate.mat]
  rw [oneMat_pGate_eq_diagonal, oneMat_pGate_eq_diagonal,
    Matrix.mul_assoc (mono _ _) (Matrix.diagonal _) (Matrix.diagonal _),
    Matrix.diagonal_mul_diagonal, cx_mul_diagonal_mul_cx]
  congr 1
  funext x
  simp only [cxFun, Function.update_self, Function.update_of_ne hab]

/-- **The Toffoli.**  Exactly (no phase): flip `t` iff `a` and `b` are both one. -/
theorem acts_ccx {a b t : Fin N} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    Acts (ccx a b t) (fun x => Function.update x t (xor (x t) (x a && x b))) := by
  unfold Acts
  rw [ccx_split, circMat_append, circMat_ccxHead hat hbt, circMat_ccxTail hab,
    ctrl2_ccxBlock hat hbt, diagonal_mul_mono]
  have hφ : ∀ x : St N,
      (if xor (Line.ccPerm a t b hat hbt x b) (Line.ccPerm a t b hat hbt x a)
          then e (-(Real.pi / 4)) else 1)
        * (if Line.ccPerm a t b hat hbt x a then e (Real.pi / 4) else 1)
        * ccxHeadPhase a b x = 1 := by
    intro x
    have h1 := e_neg_mul_self (Real.pi / 4)
    have h2 := e_mul_neg_self (Real.pi / 4)
    rw [Line.ccPerm_apply, Function.update_of_ne hat, Function.update_of_ne hbt]
    unfold ccxHeadPhase
    cases x a <;> cases x b <;> simp [h1, h2]
  exact (congrArg (mono _) (funext hφ)).trans rfl

theorem cnots_ccx {a b t : Fin N} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    cnots (ccx a b t) = 6 := by
  unfold ccx
  simp only [cnots_append, cnots_cx hab, cnots_cx hat, cnots_cx hbt, cnots]

theorem tr_ccx (a b t : Fin N) : TR (ccx a b t) 7 0 := by
  unfold ccx
  have tp := Line.tcost_pGate_quarter
  have tn := Line.tcost_pGate_neg_quarter
  exact tr_append (tr_append (tr_append (tr_append (tr_append (tr_append (tr_append
    (tr_append (tr_append (tr_append (tr_append
    (tr_one t Line.TCost.h) (tr_cx b t)) (tr_one t tn)) (tr_cx a t)) (tr_one t tp))
    (tr_cx b t)) (tr_one t tn)) (tr_cx a t))
    (TR.exact b tp (TR.exact t tp (tr_one t Line.TCost.h)))) (tr_cx a b))
    (TR.exact a tp (tr_one b tn))) (tr_cx a b)

theorem unitaryGates_ccx (a b t : Fin N) : UnitaryGates (ccx a b t) := by
  unfold ccx
  have hp : ∀ (q : Fin N) (φ : ℝ), UnitaryGates [Gate.one q (pGate φ)] :=
    fun q φ => unitaryGates_singleton_one q (Line.pGate_unitary φ)
  have hh : UnitaryGates [Gate.one t hGate] := unitaryGates_singleton_one t Line.hGate_unitary
  exact unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_append (unitaryGates_append (unitaryGates_append
    hh (unitaryGates_cx b t)) (hp t _)) (unitaryGates_cx a t)) (hp t _))
    (unitaryGates_cx b t)) (hp t _)) (unitaryGates_cx a t))
    (unitaryGates_cons_one b (Line.pGate_unitary _)
      (unitaryGates_cons_one t (Line.pGate_unitary _) hh))) (unitaryGates_cx a b))
    (unitaryGates_cons_one a (Line.pGate_unitary _) (hp b _))) (unitaryGates_cx a b)

/-! ### E. Counting for the relative-phase pieces -/

theorem ryGate_neg (φ : ℝ) : ryGate (-φ) = (ryGate φ)ᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  unfold Line.ryGate
  rw [Line.star_m2, show -φ / 2 = -(φ / 2) by ring, Real.cos_neg, Real.sin_neg]
  simp only [Complex.ofReal_neg, neg_neg, star_neg, Complex.star_def, Complex.conj_ofReal]

theorem tcost_ryGate_neg_quarter : Line.TCost (ryGate (-(Real.pi / 4))) 1 := by
  rw [ryGate_neg]
  exact Line.tcost_conjTranspose Line.tcost_ryGate_quarter

theorem cnots_ryA {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) : cnots (ryA u v s) = 2 := by
  unfold ryA
  simp only [cnots_append, cnots_cx hu, cnots_cx hv, cnots]

theorem cnots_ryAinv {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) : cnots (ryAinv u v s) = 2 := by
  unfold ryAinv
  simp only [cnots_append, cnots_cx hu, cnots_cx hv, cnots]

theorem cnots_marg {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) : cnots (marg u v s) = 3 := by
  unfold marg
  simp only [cnots_append, cnots_ryA hu hv, cnots_cx hv, cnots]

theorem tr_ryA (u v s : Fin N) : TR (ryA u v s) 2 0 :=
  tr_append (tr_append (tr_append (tr_one s tcost_ryGate_neg_quarter) (tr_cx v s))
    (tr_one s tcost_ryGate_neg_quarter)) (tr_cx u s)

theorem tr_ryAinv (u v s : Fin N) : TR (ryAinv u v s) 2 0 :=
  tr_append (tr_append (tr_append (tr_cx u s) (tr_one s Line.tcost_ryGate_quarter))
    (tr_cx v s)) (tr_one s Line.tcost_ryGate_quarter)

theorem tr_marg (u v s : Fin N) : TR (marg u v s) 4 0 :=
  tr_append (tr_append (tr_append (tr_ryA u v s) (tr_one s Line.tcost_ryGate_quarter))
    (tr_cx v s)) (tr_one s Line.tcost_ryGate_quarter)

theorem unitaryGates_ryA (u v s : Fin N) : UnitaryGates (ryA u v s) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_singleton_one s (Line.ryGate_unitary _)) (unitaryGates_cx v s))
    (unitaryGates_singleton_one s (Line.ryGate_unitary _))) (unitaryGates_cx u s)

theorem unitaryGates_ryAinv (u v s : Fin N) : UnitaryGates (ryAinv u v s) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_cx u s) (unitaryGates_singleton_one s (Line.ryGate_unitary _)))
    (unitaryGates_cx v s)) (unitaryGates_singleton_one s (Line.ryGate_unitary _))

theorem unitaryGates_marg (u v s : Fin N) : UnitaryGates (marg u v s) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_ryA u v s) (unitaryGates_singleton_one s (Line.ryGate_unitary _)))
    (unitaryGates_cx v s)) (unitaryGates_singleton_one s (Line.ryGate_unitary _))

end Qulin
