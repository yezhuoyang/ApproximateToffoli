/-
The relative-phase Toffoli cell on three neighbouring qubits of a line.

The cell is nine gates, all acting on the middle qubit `mid`, with `top` and `bot`
used only as classical controls.  Its matrix is the permutation "flip `mid` iff
`top` and `bot` are both one" up to phases of modulus one, and it has 3 CNOTs.
-/
import Mathlib
import ApproxToffoli.Line.Mono

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### 2×2 matrices from their entries -/

/-- A 2×2 matrix from its four entries (rows and columns ordered `false`, `true`). -/
def m2 (a b c d : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => if i then (if j then d else c) else (if j then b else a)

theorem m2_mul (a b c d a' b' c' d' : ℂ) :
    m2 a b c d * m2 a' b' c' d'
      = m2 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  ext i j
  cases i <;> cases j <;> simp [m2, Matrix.mul_apply] <;> ring

theorem one_eq_m2 : (1 : Matrix Bool Bool ℂ) = m2 1 0 0 1 := by
  ext i j
  cases i <;> cases j <;> simp [m2]

theorem xGate_eq_m2 : xGate = m2 0 1 1 0 := by
  ext i j
  cases i <;> cases j <;> simp [m2, xGate]

theorem pGate_eq_m2 (t : ℝ) : pGate t = m2 1 0 0 (e t) := by
  ext i j
  cases i <;> cases j <;> simp [m2, pGate]

theorem hGate_eq_m2 :
    hGate = m2 (1 / (Real.sqrt 2 : ℂ)) (1 / (Real.sqrt 2 : ℂ)) (1 / (Real.sqrt 2 : ℂ))
      (-(1 / (Real.sqrt 2 : ℂ))) := by
  ext i j
  cases i <;> cases j <;> simp [m2, hGate]

/-- Conjugation by the Hadamard gate. -/
theorem hGate_mul_mul (a b c d : ℂ) :
    hGate * m2 a b c d * hGate
      = m2 ((a + b + c + d) / 2) ((a - b + c - d) / 2) ((a + b - c - d) / 2)
          ((a - b - c + d) / 2) := by
  have hs : (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
      norm_num
    rw [div_mul_div_comm, h2, one_mul]
  rw [hGate_eq_m2, m2_mul, m2_mul]
  congr 1
  · linear_combination (a + b + c + d) * hs
  · linear_combination (a - b + c - d) * hs
  · linear_combination (a + b - c - d) * hs
  · linear_combination (a - b - c + d) * hs

/-! ### The phases `e^{±iπ/4}` -/

theorem e_pi_div_two : e (Real.pi / 2) = Complex.I := by
  unfold e
  push_cast
  exact Complex.exp_pi_div_two_mul_I

theorem e_quarter_sq : e (Real.pi / 4) * e (Real.pi / 4) = Complex.I := by
  rw [← e_add, show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring, e_pi_div_two]

theorem e_neg_quarter_sq : e (-Real.pi / 4) * e (-Real.pi / 4) = -Complex.I := by
  rw [← e_add, show -Real.pi / 4 + -Real.pi / 4 = -(Real.pi / 2) by ring, ← star_e,
    e_pi_div_two]
  simp

theorem e_quarter_mul_neg : e (Real.pi / 4) * e (-Real.pi / 4) = 1 := by
  rw [← e_add, show Real.pi / 4 + -Real.pi / 4 = 0 by ring, e_zero]

theorem e_neg_mul_quarter : e (-Real.pi / 4) * e (Real.pi / 4) = 1 := by
  rw [mul_comm, e_quarter_mul_neg]

/-! ### The 2×2 block of the cell, for each value of the two controls -/

/-- The middle seven gates: `1, 1, X, Y` for `(top, bot) = (0,0), (1,0), (0,1), (1,1)`. -/
theorem rccx_mid (t b : Bool) :
    pGate (Real.pi / 4) * (if t then xGate else 1) * pGate (-Real.pi / 4)
        * (if b then xGate else 1) * pGate (Real.pi / 4) * (if t then xGate else 1)
        * pGate (-Real.pi / 4)
      = if b then (if t then m2 0 (-Complex.I) Complex.I 0 else m2 0 1 1 0)
        else m2 1 0 0 1 := by
  cases t <;> cases b <;>
    simp only [↓reduceIte, Bool.false_eq_true, pGate_eq_m2, xGate_eq_m2, one_eq_m2, m2_mul,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, e_quarter_sq,
      e_neg_quarter_sq, e_quarter_mul_neg, e_neg_mul_quarter]

/-- The block of the whole cell: `1, 1, Z, -Y`. -/
def rccxBlock (t b : Bool) : Matrix Bool Bool ℂ :=
  if b then (if t then m2 0 Complex.I (-Complex.I) 0 else m2 1 0 0 (-1)) else m2 1 0 0 1

theorem rccx_block (t b : Bool) :
    hGate * pGate (Real.pi / 4) * (if t then xGate else 1) * pGate (-Real.pi / 4)
        * (if b then xGate else 1) * pGate (Real.pi / 4) * (if t then xGate else 1)
        * pGate (-Real.pi / 4) * hGate
      = rccxBlock t b := by
  have hre : hGate * pGate (Real.pi / 4) * (if t then xGate else 1) * pGate (-Real.pi / 4)
        * (if b then xGate else 1) * pGate (Real.pi / 4) * (if t then xGate else 1)
        * pGate (-Real.pi / 4) * hGate
      = hGate * (pGate (Real.pi / 4) * (if t then xGate else 1) * pGate (-Real.pi / 4)
        * (if b then xGate else 1) * pGate (Real.pi / 4) * (if t then xGate else 1)
        * pGate (-Real.pi / 4)) * hGate := by
    simp only [Matrix.mul_assoc]
  rw [hre, rccx_mid]
  cases t <;> cases b <;>
    simp only [↓reduceIte, Bool.false_eq_true, hGate_mul_mul, rccxBlock] <;>
    congr 1 <;> ring

/-! ### Blocks on `mid` controlled classically by `top` and `bot` -/

/-- The block `G (x top) (x bot)` applied to qubit `mid`. -/
def ctrl2 (top mid bot : Fin N) (G : Bool → Bool → Matrix Bool Bool ℂ) :
    Matrix (St N) (St N) ℂ :=
  ctrlMat mid (fun x => G (x top) (x bot))

theorem ctrl2_mul (top mid bot : Fin N) (ht : top ≠ mid) (hb : bot ≠ mid)
    (G G' : Bool → Bool → Matrix Bool Bool ℂ) :
    ctrl2 top mid bot G * ctrl2 top mid bot G'
      = ctrl2 top mid bot (fun t b => G t b * G' t b) := by
  refine ctrlMat_mul mid _ _ (fun x b => ?_)
  change G (Function.update x mid b top) (Function.update x mid b bot) = G (x top) (x bot)
  rw [Function.update_of_ne ht, Function.update_of_ne hb]

theorem one_eq_ctrl2 (top mid bot : Fin N) (g : Matrix Bool Bool ℂ) :
    (Gate.one mid g).mat = ctrl2 top mid bot (fun _ _ => g) := rfl

theorem cx_top_eq_ctrl2 (top mid bot : Fin N)
    (adj : top.val + 1 = mid.val ∨ mid.val + 1 = top.val) :
    (Gate.cx top mid adj).mat = ctrl2 top mid bot (fun t _ => if t then xGate else 1) :=
  cx_eq_ctrlMat top mid (adj_ne adj)

theorem cx_bot_eq_ctrl2 (top mid bot : Fin N)
    (adj : bot.val + 1 = mid.val ∨ mid.val + 1 = bot.val) :
    (Gate.cx bot mid adj).mat = ctrl2 top mid bot (fun _ b => if b then xGate else 1) :=
  cx_eq_ctrlMat bot mid (adj_ne adj)

/-! ### The cell -/

/-- The relative-phase Toffoli cell: nine gates on `mid`, three of them CNOTs. -/
noncomputable def rccx (top mid bot : Fin N)
    (h1 : top.val + 1 = mid.val ∨ mid.val + 1 = top.val)
    (h2 : bot.val + 1 = mid.val ∨ mid.val + 1 = bot.val) : List (Gate N) :=
  [.one mid hGate, .one mid (pGate (-Real.pi / 4)), .cx top mid h1,
   .one mid (pGate (Real.pi / 4)), .cx bot mid h2, .one mid (pGate (-Real.pi / 4)),
   .cx top mid h1, .one mid (pGate (Real.pi / 4)), .one mid hGate]

theorem cnots_rccx (top mid bot : Fin N)
    (h1 : top.val + 1 = mid.val ∨ mid.val + 1 = top.val)
    (h2 : bot.val + 1 = mid.val ∨ mid.val + 1 = bot.val) :
    cnots (rccx top mid bot h1 h2) = 3 := rfl

theorem circMat_rccx_ctrl2 (top mid bot : Fin N)
    (h1 : top.val + 1 = mid.val ∨ mid.val + 1 = top.val)
    (h2 : bot.val + 1 = mid.val ∨ mid.val + 1 = bot.val) :
    circMat (rccx top mid bot h1 h2) = ctrl2 top mid bot rccxBlock := by
  simp only [rccx, circMat, one_mul, one_eq_ctrl2 top mid bot, cx_top_eq_ctrl2 top mid bot,
    cx_bot_eq_ctrl2 top mid bot, ctrl2_mul top mid bot (adj_ne h1) (adj_ne h2)]
  congr 1
  funext t b
  exact rccx_block t b

/-- The basis permutation of the cell: flip bit `mid` iff bits `top` and `bot` are
both one. -/
def ccPerm (top mid bot : Fin N) (ht : top ≠ mid) (hb : bot ≠ mid) : Equiv.Perm (St N) :=
  flipPerm mid (fun x => x top && x bot) (fun x b => by
    change (Function.update x mid b top && Function.update x mid b bot) = (x top && x bot)
    rw [Function.update_of_ne ht, Function.update_of_ne hb])

theorem ccPerm_apply (top mid bot : Fin N) (ht : top ≠ mid) (hb : bot ≠ mid) (x : St N) :
    ccPerm top mid bot ht hb x
      = Function.update x mid (xor (x mid) (x top && x bot)) := rfl

/-- The phases of the cell. -/
noncomputable def rccxPhase (top mid bot : Fin N) (x : St N) : ℂ :=
  if x bot then
    (if x top then (if x mid then Complex.I else -Complex.I)
     else (if x mid then -1 else 1))
  else 1

theorem rccxPhase_unit (top mid bot : Fin N) (x : St N) :
    star (rccxPhase top mid bot x) * rccxPhase top mid bot x = 1 := by
  unfold rccxPhase
  cases x bot <;> cases x top <;> cases x mid <;> simp

/-- **The relative-phase Toffoli cell is a Toffoli up to phases.**  Its matrix sends
the basis state `x` to `rccxPhase x` times the basis state with bit `mid` flipped iff
bits `top` and `bot` are both one. -/
theorem circMat_rccx (top mid bot : Fin N)
    (h1 : top.val + 1 = mid.val ∨ mid.val + 1 = top.val)
    (h2 : bot.val + 1 = mid.val ∨ mid.val + 1 = bot.val) :
    circMat (rccx top mid bot h1 h2)
      = mono (ccPerm top mid bot (adj_ne h1) (adj_ne h2)) (rccxPhase top mid bot) := by
  have hg : ∀ (x : St N) (a b : Bool), a ≠ xor b (x top && x bot) →
      rccxBlock (x top) (x bot) a b = 0 := by
    intro x a b
    unfold rccxBlock
    cases x top <;> cases x bot <;> cases a <;> cases b <;> simp [m2]
  rw [circMat_rccx_ctrl2, ctrl2, ccPerm, ctrlMat_eq_mono mid (fun x => x top && x bot) _ _ hg]
  · congr 1
    funext x
    unfold rccxPhase rccxBlock
    cases x bot <;> cases x top <;> cases x mid <;> simp [m2]
  · intro x b
    change (Function.update x mid b top && Function.update x mid b bot) = (x top && x bot)
    rw [Function.update_of_ne (adj_ne h1), Function.update_of_ne (adj_ne h2)]

end Line
