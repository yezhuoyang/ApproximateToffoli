/-
The phase operation on a line: control wire `0`, data wires `1 .. m`.

* `fan N m` is the CNOT staircase `cx (m-1) m, …, cx 1 2, cx 0 1, cx 1 2, …, cx (m-1) m`
  (`2m - 1` adjacent CNOTs).  On basis states it adds the bit of wire `0` to each of the
  wires `1 .. m`, and it is its own inverse.
* `phaseOp N m ang` is: phase gates, `fan`, phase gates, `fan`.  It has `4m - 2` CNOTs
  and its matrix is the diagonal with entries `e (∑_{j=1}^{m} ang j · [x 0] · [x j])`.
-/
import Mathlib
import ApproxToffoli.Line.Carry

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### One CNOT `cx j (j+1)` -/

/-- The CNOT with control `j` and target `j + 1` (empty if there is no such wire). -/
def cxUp (N j : ℕ) : List (Gate N) :=
  if h : j + 1 < N then [Gate.cx ⟨j, by omega⟩ ⟨j + 1, h⟩ (Or.inl rfl)] else []

/-- The basis permutation of `cxUp N j`. -/
def cxUpPerm (N j : ℕ) : Equiv.Perm (St N) :=
  if h : j + 1 < N then
    cxPerm ⟨j, by omega⟩ ⟨j + 1, h⟩ (fin_ne (by omega) h (by omega))
  else 1

theorem circMat_cxUp (N j : ℕ) :
    circMat (cxUp N j) = mono (cxUpPerm N j) (fun _ => (1 : ℂ)) := by
  by_cases h : j + 1 < N
  · rw [cxUp, dif_pos h, cxUpPerm, dif_pos h]
    show 1 * mono _ _ = _
    rw [Matrix.one_mul]
  · rw [cxUp, dif_neg h, cxUpPerm, dif_neg h, circMat, mono_one]

theorem cnots_cxUp (j : ℕ) (h : j + 1 < N) : cnots (cxUp N j) = 1 := by
  rw [cxUp, dif_pos h]
  rfl

theorem unitaryGates_cxUp (N j : ℕ) : UnitaryGates (cxUp N j) := by
  unfold cxUp
  split_ifs
  · exact unitaryGates_cons_cx _ _ _ unitaryGates_nil
  · exact unitaryGates_nil

theorem wire_cxUpPerm (j : ℕ) (h : j + 1 < N) (x : St N) (i : ℕ) :
    wire (cxUpPerm N j x) i
      = if i = j + 1 then xor (wire x (j + 1)) (wire x j) else wire x i := by
  rw [cxUpPerm, dif_pos h, cxPerm_apply, wire_update, wire_mk x (j + 1) h,
    wire_mk x j (by omega)]

/-! ### The staircase -/

/-- `fanAux N k`: the staircase on wires `0 .. k + 1`. -/
def fanAux (N : ℕ) : ℕ → List (Gate N)
  | 0 => cxUp N 0
  | k + 1 => cxUp N (k + 1) ++ fanAux N k ++ cxUp N (k + 1)

/-- The basis permutation of `fanAux N k`. -/
def fanPerm (N : ℕ) : ℕ → Equiv.Perm (St N)
  | 0 => cxUpPerm N 0
  | k + 1 => cxUpPerm N (k + 1) * fanPerm N k * cxUpPerm N (k + 1)

/-- The CNOT staircase `cx (m-1) m, …, cx 1 2, cx 0 1, cx 1 2, …, cx (m-1) m`. -/
def fan (N m : ℕ) : List (Gate N) := fanAux N (m - 1)

theorem circMat_fanAux (N k : ℕ) :
    circMat (fanAux N k) = mono (fanPerm N k) (fun _ => (1 : ℂ)) := by
  induction k with
  | zero => exact circMat_cxUp N 0
  | succ k ih =>
    show circMat (cxUp N (k + 1) ++ fanAux N k ++ cxUp N (k + 1))
      = mono (cxUpPerm N (k + 1) * fanPerm N k * cxUpPerm N (k + 1)) _
    rw [circMat_append, circMat_append, ih, circMat_cxUp, mono_mul, mono_mul]
    simp only [mul_one, mul_assoc]

theorem cnots_fanAux (k : ℕ) (h : k + 1 < N) : cnots (fanAux N k) = 2 * k + 1 := by
  induction k with
  | zero => exact cnots_cxUp 0 h
  | succ k ih =>
    show cnots (cxUp N (k + 1) ++ fanAux N k ++ cxUp N (k + 1)) = _
    rw [cnots_append, cnots_append, ih (by omega), cnots_cxUp (k + 1) h]
    omega

theorem unitaryGates_fanAux (N k : ℕ) : UnitaryGates (fanAux N k) := by
  induction k with
  | zero => exact unitaryGates_cxUp N 0
  | succ k ih =>
    exact unitaryGates_append (unitaryGates_append (unitaryGates_cxUp N _) ih)
      (unitaryGates_cxUp N _)

theorem bool_xor3 (a b c : Bool) : xor (xor a b) (xor b c) = xor a c := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The staircase adds the bit of wire `0` to each of the wires `1 .. k + 1`. -/
theorem wire_fanPerm (k : ℕ) (h : k + 1 < N) (x : St N) (i : ℕ) :
    wire (fanPerm N k x) i
      = if 1 ≤ i ∧ i ≤ k + 1 then xor (wire x i) (wire x 0) else wire x i := by
  induction k generalizing x i with
  | zero =>
    show wire (cxUpPerm N 0 x) i = _
    rw [wire_cxUpPerm 0 h]
    split_ifs <;> first | rfl | omega | (subst_vars; rfl)
  | succ k ih =>
    have hk : k + 1 < N := by omega
    show wire (cxUpPerm N (k + 1) (fanPerm N k (cxUpPerm N (k + 1) x))) i = _
    simp only [wire_cxUpPerm (k + 1) h, ih hk]
    split_ifs <;> first | rfl | contradiction | omega | (subst_vars; exact bool_xor3 _ _ _)

/-- The staircase is its own inverse. -/
theorem fanPerm_fanPerm (k : ℕ) (h : k + 1 < N) (x : St N) :
    fanPerm N k (fanPerm N k x) = x := by
  apply wire_ext
  intro i
  rw [wire_fanPerm k h, wire_fanPerm k h, wire_fanPerm k h]
  have h0 : ¬ (1 ≤ 0 ∧ 0 ≤ k + 1) := by omega
  rw [if_neg h0]
  split_ifs
  · cases wire x i <;> cases wire x 0 <;> rfl
  · rfl

/-- Conjugating a diagonal by the staircase permutes its entries. -/
theorem fan_conj (k : ℕ) (h : k + 1 < N) (φ : St N → ℂ) :
    mono (fanPerm N k) (fun _ => (1 : ℂ)) * mono 1 φ * mono (fanPerm N k) (fun _ => (1 : ℂ))
      = mono 1 (fun x => φ (fanPerm N k x)) := by
  rw [mono_mul, mono_mul, mul_one]
  congr 1
  · exact Equiv.ext (fanPerm_fanPerm k h)
  · funext x
    simp

theorem mono_one_mul_mono_one (φ ψ : St N → ℂ) :
    mono 1 φ * mono 1 ψ = mono 1 (fun x => φ x * ψ x) := by
  rw [mono_one_eq_diagonal, mono_one_eq_diagonal, mono_one_eq_diagonal,
    Matrix.diagonal_mul_diagonal]

/-! ### Phase gates -/

/-- The phase gate `P(t)` on wire `j` (empty if there is no such wire). -/
noncomputable def pOne (N j : ℕ) (t : ℝ) : List (Gate N) :=
  if h : j < N then [Gate.one ⟨j, h⟩ (pGate t)] else []

theorem circMat_pOne (N j : ℕ) (t : ℝ) :
    circMat (pOne N j t) = mono 1 (fun x => if wire x j then e t else 1) := by
  by_cases h : j < N
  · rw [pOne, dif_pos h]
    show 1 * oneMat _ _ = _
    rw [Matrix.one_mul, oneMat_pGate]
    congr 1
    funext x
    rw [wire_mk x j h]
  · have hf : (fun x : St N => if wire x j then e t else (1 : ℂ)) = fun _ => 1 := by
      funext x
      rw [wire, dif_neg h]
      simp
    rw [pOne, dif_neg h, circMat, hf, mono_one]

theorem cnots_pOne (N j : ℕ) (t : ℝ) : cnots (pOne N j t) = 0 := by
  unfold pOne
  split_ifs <;> rfl

theorem unitaryGates_pOne (N j : ℕ) (t : ℝ) : UnitaryGates (pOne N j t) := by
  unfold pOne
  split_ifs
  · exact unitaryGates_cons_one _ (pGate_unitary t) unitaryGates_nil
  · exact unitaryGates_nil

/-- Phase gates `P(f j)` on the wires `j = 1 .. n`. -/
noncomputable def pLayer (N : ℕ) (f : ℕ → ℝ) : ℕ → List (Gate N)
  | 0 => []
  | n + 1 => pLayer N f n ++ pOne N (n + 1) (f (n + 1))

theorem circMat_pLayer (N : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    circMat (pLayer N f n)
      = mono 1 (fun x => e (∑ j ∈ Finset.Icc 1 n, if wire x j then f j else 0)) := by
  induction n with
  | zero =>
    have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    show (1 : Matrix (St N) (St N) ℂ) = _
    simp only [h0, Finset.sum_empty, e_zero, mono_one]
  | succ n ih =>
    show circMat (pLayer N f n ++ pOne N (n + 1) (f (n + 1))) = _
    rw [circMat_append, ih, circMat_pOne, mono_one_mul_mono_one]
    congr 1
    funext x
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), e_add, mul_comm]
    congr 1
    cases wire x (n + 1) <;> simp [e_zero]

theorem cnots_pLayer (N : ℕ) (f : ℕ → ℝ) (n : ℕ) : cnots (pLayer N f n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show cnots (pLayer N f n ++ pOne N (n + 1) (f (n + 1))) = 0
    rw [cnots_append, ih, cnots_pOne]

theorem unitaryGates_pLayer (N : ℕ) (f : ℕ → ℝ) (n : ℕ) : UnitaryGates (pLayer N f n) := by
  induction n with
  | zero => exact unitaryGates_nil
  | succ n ih => exact unitaryGates_append ih (unitaryGates_pOne N _ _)

/-! ### The phase operation -/

/-- **The phase operation.**  Control wire `0`, data wires `1 .. m`, angles `ang j`. -/
noncomputable def phaseOp (N m : ℕ) (ang : ℕ → ℝ) : List (Gate N) :=
  pOne N 0 ((∑ j ∈ Finset.Icc 1 m, ang j) / 2) ++ pLayer N (fun j => ang j / 2) m
    ++ fan N m ++ pLayer N (fun j => -(ang j) / 2) m ++ fan N m

theorem cnots_phaseOp (m : ℕ) (hm : 1 ≤ m) (hN : m + 1 ≤ N) (ang : ℕ → ℝ) :
    cnots (phaseOp N m ang) = 4 * m - 2 := by
  have hk : m - 1 + 1 < N := by omega
  unfold phaseOp fan
  rw [cnots_append, cnots_append, cnots_append, cnots_append, cnots_fanAux _ hk,
    cnots_pLayer, cnots_pLayer, cnots_pOne]
  omega

theorem unitaryGates_phaseOp (N m : ℕ) (ang : ℕ → ℝ) : UnitaryGates (phaseOp N m ang) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_pOne N _ _) (unitaryGates_pLayer N _ _)) (unitaryGates_fanAux N _))
    (unitaryGates_pLayer N _ _)) (unitaryGates_fanAux N _)

/-- The arithmetic of the phases: `b·q = (b + q − (b ⊕ q)) / 2` on each data wire. -/
theorem phase_arith (m : ℕ) (ang : ℕ → ℝ) (b : Bool) (w : ℕ → Bool) :
    e (∑ j ∈ Finset.Icc 1 m, if xor (w j) b then -(ang j) / 2 else 0)
        * (e (∑ j ∈ Finset.Icc 1 m, if w j then ang j / 2 else 0)
          * (if b then e ((∑ j ∈ Finset.Icc 1 m, ang j) / 2) else 1))
      = if b then e (∑ j ∈ Finset.Icc 1 m, if w j then ang j else 0) else 1 := by
  have hterm : ∀ j, (if xor (w j) b then -(ang j) / 2 else 0)
      + ((if w j then ang j / 2 else 0) + (if b then ang j / 2 else 0))
      = if b then (if w j then ang j else 0) else 0 := by
    intro j
    cases w j <;> cases b <;> simp <;> ring
  have hb : (if b then e ((∑ j ∈ Finset.Icc 1 m, ang j) / 2) else 1)
      = e (∑ j ∈ Finset.Icc 1 m, if b then ang j / 2 else 0) := by
    cases b
    · simp [e_zero]
    · simp [Finset.sum_div]
  have hr : (if b then e (∑ j ∈ Finset.Icc 1 m, if w j then ang j else 0) else 1)
      = e (∑ j ∈ Finset.Icc 1 m, if b then (if w j then ang j else 0) else 0) := by
    cases b <;> simp [e_zero]
  rw [hb, hr, ← e_add, ← e_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact congrArg e (Finset.sum_congr rfl (fun j _ => hterm j))

theorem mul5_assoc (A B C D E : Matrix (St N) (St N) ℂ) :
    A * (B * (C * (D * E))) = A * B * C * (D * E) := by
  simp only [Matrix.mul_assoc]

/-- **The phase operation is diagonal**: on the basis state `x` its entry is
`e (∑_{j=1}^{m} ang j · [x 0] · [x j])`. -/
theorem circMat_phaseOp (m : ℕ) (hm : 1 ≤ m) (hN : m + 1 ≤ N) (ang : ℕ → ℝ) :
    circMat (phaseOp N m ang)
      = Matrix.diagonal (fun x : St N =>
          if wire x 0 then e (∑ j ∈ Finset.Icc 1 m, if wire x j then ang j else 0) else 1) := by
  have hk : m - 1 + 1 < N := by omega
  unfold phaseOp fan
  rw [circMat_append, circMat_append, circMat_append, circMat_append, circMat_fanAux,
    circMat_pLayer, circMat_pLayer, circMat_pOne, mul5_assoc, fan_conj _ hk,
    mono_one_mul_mono_one, mono_one_mul_mono_one, mono_one_eq_diagonal]
  congr 1
  funext x
  have hs : (∑ j ∈ Finset.Icc 1 m,
        if wire (fanPerm N (m - 1) x) j then -(ang j) / 2 else 0)
      = ∑ j ∈ Finset.Icc 1 m, if xor (wire x j) (wire x 0) then -(ang j) / 2 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hc : 1 ≤ j ∧ j ≤ m - 1 + 1 := ⟨hj.1, by omega⟩
    rw [wire_fanPerm _ hk, if_pos hc]
  rw [hs]
  exact phase_arith m ang (wire x 0) (fun j => wire x j)

/-- The inverse circuit is the diagonal with the conjugate entries. -/
theorem circMat_invCirc_phaseOp (m : ℕ) (hm : 1 ≤ m) (hN : m + 1 ≤ N) (ang : ℕ → ℝ) :
    circMat (invCirc (phaseOp N m ang))
      = Matrix.diagonal (fun x : St N =>
          if wire x 0 then e (∑ j ∈ Finset.Icc 1 m, if wire x j then -(ang j) else 0)
          else 1) := by
  rw [circMat_invCirc, circMat_phaseOp m hm hN, Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  show star (if wire x 0 = true then
      e (∑ j ∈ Finset.Icc 1 m, if wire x j = true then ang j else 0) else 1) = _
  by_cases h0 : wire x 0 = true
  · rw [if_pos h0, if_pos h0, star_e, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  · rw [if_neg h0, if_neg h0, star_one]

end Line
