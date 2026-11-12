/-
Inverse circuits and unitarity bookkeeping for circuits on a line.

* `invCirc c` reverses the circuit and replaces every one-qubit gate by its conjugate
  transpose; its matrix is `(circMat c)ᴴ` and it has the same number of CNOTs.
* `UnitaryGates` is closed under append and `invCirc`; `hGate`, `pGate t`, `xGate`
  are unitary.
* Conjugating a diagonal by a permutation up to unit phases permutes its entries.
* A one-qubit gate commutes with a CNOT that does not touch its qubit.
-/
import Mathlib
import ApproxToffoli.Line.Rccx

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### Inverse gates and circuits -/

/-- The inverse of a gate: a CNOT is its own inverse, a one-qubit gate is replaced by
its conjugate transpose. -/
def Gate.inv : Gate N → Gate N
  | .cx c t adj => .cx c t adj
  | .one q g => .one q gᴴ

/-- The inverse circuit: inverse gates in the reverse order. -/
def invCirc (c : List (Gate N)) : List (Gate N) := (c.map Gate.inv).reverse

theorem invCirc_nil : invCirc ([] : List (Gate N)) = [] := rfl

theorem invCirc_cons (g : Gate N) (c : List (Gate N)) :
    invCirc (g :: c) = invCirc c ++ [g.inv] := by
  simp [invCirc]

theorem conjTranspose_oneMat (q : Fin N) (g : Matrix Bool Bool ℂ) :
    (oneMat q g)ᴴ = oneMat q gᴴ := by
  ext y x
  simp only [conjTranspose_apply, oneMat, of_apply]
  by_cases h : ∀ r, r ≠ q → y r = x r
  · have h' : ∀ r, r ≠ q → x r = y r := fun r hr => (h r hr).symm
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ r, r ≠ q → x r = y r := fun h' => h fun r hr => (h' r hr).symm
    rw [if_neg h, if_neg h', star_zero]

theorem cxPerm_apply (c t : Fin N) (h : c ≠ t) (x : St N) :
    cxPerm c t h x = Function.update x t (xor (x t) (x c)) := rfl

theorem cxPerm_cxPerm (c t : Fin N) (h : c ≠ t) (x : St N) :
    cxPerm c t h (cxPerm c t h x) = x := cxFun_involutive c t h x

theorem conjTranspose_cx (c t : Fin N) (h : c ≠ t) :
    (mono (cxPerm c t h) (fun _ => (1 : ℂ)))ᴴ = mono (cxPerm c t h) (fun _ => (1 : ℂ)) := by
  ext y x
  simp only [conjTranspose_apply, mono, of_apply]
  have key : x = cxPerm c t h y ↔ y = cxPerm c t h x := by
    constructor
    · intro hx
      rw [hx, cxPerm_cxPerm]
    · intro hy
      rw [hy, cxPerm_cxPerm]
  by_cases hx : x = cxPerm c t h y
  · rw [if_pos hx, if_pos (key.1 hx), star_one]
  · rw [if_neg hx, if_neg (fun hy => hx (key.2 hy)), star_zero]

theorem conjTranspose_gate_mat (g : Gate N) : g.matᴴ = g.inv.mat := by
  cases g with
  | cx c t adj => exact conjTranspose_cx c t (adj_ne adj)
  | one q m => exact conjTranspose_oneMat q m

/-- The matrix of the inverse circuit is the conjugate transpose. -/
theorem circMat_invCirc (c : List (Gate N)) : circMat (invCirc c) = (circMat c)ᴴ := by
  induction c with
  | nil => simp [invCirc, circMat]
  | cons g c ih =>
    rw [invCirc_cons, circMat_append, ih]
    simp only [circMat, one_mul, conjTranspose_mul, conjTranspose_gate_mat]

/-- The inverse circuit has the same number of CNOTs. -/
theorem cnots_invCirc (c : List (Gate N)) : cnots (invCirc c) = cnots c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    rw [invCirc_cons, cnots_append, ih]
    cases g <;> simp [cnots, Gate.inv]

/-! ### Unitarity bookkeeping -/

theorem unitaryGates_nil : UnitaryGates ([] : List (Gate N)) := by
  intro g hg
  simp at hg

theorem unitaryGates_append {c d : List (Gate N)} (hc : UnitaryGates c)
    (hd : UnitaryGates d) : UnitaryGates (c ++ d) := by
  intro g hg q m hgm
  rcases List.mem_append.1 hg with h | h
  · exact hc g h q m hgm
  · exact hd g h q m hgm

theorem unitaryGates_cons_cx (c t : Fin N) (adj : c.val + 1 = t.val ∨ t.val + 1 = c.val)
    {l : List (Gate N)} (hl : UnitaryGates l) : UnitaryGates (Gate.cx c t adj :: l) := by
  intro g hg q m hgm
  rcases List.mem_cons.1 hg with h | h
  · rw [h] at hgm
    cases hgm
  · exact hl g h q m hgm

theorem unitaryGates_cons_one (q : Fin N) {m : Matrix Bool Bool ℂ}
    (hm : m ∈ Matrix.unitaryGroup Bool ℂ) {l : List (Gate N)} (hl : UnitaryGates l) :
    UnitaryGates (Gate.one q m :: l) := by
  intro g hg q' m' hgm
  rcases List.mem_cons.1 hg with h | h
  · rw [h] at hgm
    injection hgm with h1 h2
    rw [← h2]
    exact hm
  · exact hl g h q' m' hgm

theorem unitaryGates_invCirc {c : List (Gate N)} (hc : UnitaryGates c) :
    UnitaryGates (invCirc c) := by
  intro g hg q m hgm
  unfold invCirc at hg
  rw [List.mem_reverse, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  cases g' with
  | cx c' t adj => cases hgm
  | one q' m' =>
    injection hgm with h1 h2
    rw [← h2]
    exact Unitary.star_mem (hc _ hg' q' m' rfl)

theorem star_m2 (a b c d : ℂ) : star (m2 a b c d) = m2 (star a) (star c) (star b) (star d) := by
  ext i j
  cases i <;> cases j <;> simp [m2, Matrix.star_apply]

theorem hGate_unitary : hGate ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star hGate = hGate := by
    rw [hGate_eq_m2, star_m2]
    simp
  have h := hGate_mul_mul 1 0 0 1
  rw [← one_eq_m2, Matrix.mul_one] at h
  rw [hs, h, one_eq_m2]
  congr 1 <;> norm_num

theorem xGate_unitary : xGate ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, xGate_eq_m2, star_m2, one_eq_m2]
  simp [m2_mul]

theorem pGate_unitary (t : ℝ) : pGate t ∈ Matrix.unitaryGroup Bool ℂ := by
  have he : e t * (starRingEnd ℂ) (e t) = 1 := by
    change e t * star (e t) = 1
    rw [star_e, ← e_add, add_neg_cancel, e_zero]
  rw [Matrix.mem_unitaryGroup_iff, pGate_eq_m2, star_m2, one_eq_m2, m2_mul]
  simp [he]

theorem unitaryGates_rccx (top mid bot : Fin N)
    (h1 : top.val + 1 = mid.val ∨ mid.val + 1 = top.val)
    (h2 : bot.val + 1 = mid.val ∨ mid.val + 1 = bot.val) :
    UnitaryGates (rccx top mid bot h1 h2) := by
  unfold rccx
  repeat first
    | exact unitaryGates_nil
    | apply unitaryGates_cons_cx
    | apply unitaryGates_cons_one _ hGate_unitary
    | apply unitaryGates_cons_one _ (pGate_unitary _)

/-! ### Conjugating a diagonal by a permutation up to phases -/

theorem mono_one_eq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → ℂ) :
    mono (1 : Equiv.Perm ι) φ = Matrix.diagonal φ := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [mono]
  · simp [mono, h]

/-- `Vᴴ * D * V` for `V` a permutation up to unit phases and `D` diagonal: the diagonal
entries are permuted and the phases cancel. -/
theorem conj_mono_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (φ β : ι → ℂ) (hφ : ∀ x, star (φ x) * φ x = 1) :
    (mono σ φ)ᴴ * Matrix.diagonal β * mono σ φ = Matrix.diagonal (fun x => β (σ x)) := by
  ext i j
  rw [Matrix.mul_assoc, conjTranspose_mono_mul_apply, mul_mono_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    linear_combination β (σ i) * hφ i
  · have h' : σ i ≠ σ j := fun hh => h (σ.injective hh)
    rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h']
    simp

theorem mono_mul_apply' {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (φ : ι → ℂ) (M : Matrix ι ι ℂ) (i j : ι) :
    (mono σ φ * M) i j = φ (σ.symm i) * M (σ.symm i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm i)]
  · simp [mono]
  · intro k _ hk
    have hik : i ≠ σ k := fun h => hk (by rw [h]; simp)
    simp [mono, hik]
  · simp

/-! ### A one-qubit gate commutes with a CNOT on other qubits -/

theorem cxPerm_agree (q c t : Fin N) (h : c ≠ t) (hqc : q ≠ c) (hqt : q ≠ t) (y x : St N)
    (hA : ∀ r, r ≠ q → y r = x r) : ∀ r, r ≠ q → cxPerm c t h y r = cxPerm c t h x r := by
  intro r hr
  rw [cxPerm_apply, cxPerm_apply]
  by_cases hrt : r = t
  · rw [hrt, Function.update_self, Function.update_self, hA t (Ne.symm hqt),
      hA c (Ne.symm hqc)]
  · rw [Function.update_of_ne hrt, Function.update_of_ne hrt]
    exact hA r hr

theorem oneMat_mul_cx_comm (q c t : Fin N) (h : c ≠ t) (hqc : q ≠ c) (hqt : q ≠ t)
    (g : Matrix Bool Bool ℂ) :
    oneMat q g * mono (cxPerm c t h) (fun _ => (1 : ℂ))
      = mono (cxPerm c t h) (fun _ => (1 : ℂ)) * oneMat q g := by
  ext y x
  rw [mul_mono_apply, mono_mul_apply', mul_one, one_mul]
  have hs : (cxPerm c t h).symm y = cxPerm c t h y := rfl
  rw [hs]
  simp only [oneMat, of_apply]
  have hq1 : cxPerm c t h x q = x q := by rw [cxPerm_apply, Function.update_of_ne hqt]
  have hq2 : cxPerm c t h y q = y q := by rw [cxPerm_apply, Function.update_of_ne hqt]
  by_cases hA : ∀ r, r ≠ q → y r = cxPerm c t h x r
  · have hB : ∀ r, r ≠ q → cxPerm c t h y r = x r := by
      intro r hr
      have := cxPerm_agree q c t h hqc hqt _ _ hA r hr
      rwa [cxPerm_cxPerm] at this
    rw [if_pos hA, if_pos hB, hq1, hq2]
  · have hB : ¬ ∀ r, r ≠ q → cxPerm c t h y r = x r := by
      intro hB
      apply hA
      intro r hr
      have := cxPerm_agree q c t h hqc hqt _ _ hB r hr
      rwa [cxPerm_cxPerm] at this
    rw [if_neg hA, if_neg hB]

/-- A one-qubit gate on `q` commutes with a CNOT that does not touch `q`. -/
theorem one_mat_mul_cx_mat_comm (q c t : Fin N)
    (adj : c.val + 1 = t.val ∨ t.val + 1 = c.val) (hqc : q ≠ c) (hqt : q ≠ t)
    (g : Matrix Bool Bool ℂ) :
    (Gate.one q g).mat * (Gate.cx c t adj).mat = (Gate.cx c t adj).mat * (Gate.one q g).mat :=
  oneMat_mul_cx_comm q c t (adj_ne adj) hqc hqt g

end Line
