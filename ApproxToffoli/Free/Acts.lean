/-
Circuits that act on basis states as a function (classical reversible circuits), and
the vocabulary used to state what the blocks of the Huang–Palsberg circuit do.

Definitions (fixed).  Lemmas about them are added below the definitions.
-/
import Mathlib
import ApproxToffoli.Free.Model
import ApproxToffoli.Line.Mono

namespace Free

open Matrix
open Line (St)

variable {N : ℕ}

/-- The matrix that sends basis state `x` to basis state `f x`. -/
def permMat (f : St N → St N) : Matrix (St N) (St N) ℂ :=
  Matrix.of fun y x => if y = f x then 1 else 0

/-- The circuit `c` sends every basis state `x` to the basis state `f x`, with no phase. -/
def Acts (c : List (Gate N)) (f : St N → St N) : Prop := circMat c = permMat f

/-- The number held by the register `q 0, ..., q (m-1)` (`q 0` is the low bit). -/
def regVal (m : ℕ) (q : ℕ → Fin N) (x : St N) : ℕ :=
  ∑ i ∈ Finset.range m, if x (q i) = true then 2 ^ i else 0

/-- The qubits `q 0, ..., q (m-1)` are distinct. -/
def Inj (m : ℕ) (q : ℕ → Fin N) : Prop := ∀ i < m, ∀ j < m, q i = q j → i = j

/-- No qubit of `q 0, ..., q (m-1)` is one of `g 0, ..., g (m'-1)`. -/
def Disj (m : ℕ) (q : ℕ → Fin N) (m' : ℕ) (g : ℕ → Fin N) : Prop :=
  ∀ i < m, ∀ j < m', q i ≠ g j

/-- The function `f` on basis states adds `d x` (modulo `2 ^ m`) to the register
`q 0, ..., q (m-1)` and leaves every other qubit unchanged. -/
def AddsTo (m : ℕ) (q : ℕ → Fin N) (d : St N → ℕ) (f : St N → St N) : Prop :=
  ∀ x, regVal m q (f x) = (regVal m q x + d x) % 2 ^ m ∧
    ∀ r, (∀ i < m, r ≠ q i) → f x r = x r

/-! ### Lemmas: permutation matrices and `Acts` -/

theorem permMat_apply (f : St N → St N) (y x : St N) :
    permMat f y x = if y = f x then 1 else 0 := rfl

theorem permMat_id : permMat (id : St N → St N) = 1 := by
  ext y x
  simp [permMat, Matrix.one_apply]

theorem permMat_mul (g f : St N → St N) : permMat g * permMat f = permMat (g ∘ f) := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single (f x)]
  · simp [permMat]
  · intro z _ hz
    simp [permMat, hz]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mono_one_eq_permMat (σ : Equiv.Perm (St N)) :
    ExactLine.mono σ (fun _ => 1) = permMat σ := rfl

theorem permMat_injective {f g : St N → St N} (h : permMat f = permMat g) : f = g := by
  funext x
  have h1 := congrFun (congrFun h (f x)) x
  simp only [permMat_apply, if_true] at h1
  by_contra hne
  rw [if_neg hne] at h1
  exact one_ne_zero h1

theorem circMat_singleton (g : Gate N) : circMat [g] = g.mat := by
  simp [circMat]

theorem circMat_cons (g : Gate N) (c : List (Gate N)) : circMat (g :: c) = circMat c * g.mat :=
  rfl

theorem acts_nil : Acts ([] : List (Gate N)) id := by
  unfold Acts
  rw [permMat_id]
  rfl

theorem acts_append {c d : List (Gate N)} {f g : St N → St N} (hc : Acts c f) (hd : Acts d g) :
    Acts (c ++ d) (g ∘ f) := by
  unfold Acts at *
  rw [circMat_append, hc, hd, permMat_mul]

/-- `Acts` with the function replaced by an equal one. -/
theorem Acts.congr {c : List (Gate N)} {f g : St N → St N} (hc : Acts c f) (h : ∀ x, f x = g x) :
    Acts c g := by
  rw [← funext h]
  exact hc

/-- The function of a circuit is unique. -/
theorem Acts.unique {c : List (Gate N)} {f g : St N → St N} (hf : Acts c f) (hg : Acts c g) :
    f = g := permMat_injective (hf.symm.trans hg)

/-- A CNOT acts as `cxFun`. -/
theorem acts_cx_gate (c t : Fin N) (h : c ≠ t) : Acts [Gate.cx c t h] (Line.cxFun c t) := by
  unfold Acts
  rw [circMat_singleton]
  rfl

/-! ### Lemmas: unitary gates, T accounting -/

theorem unitaryGates_nil : UnitaryGates ([] : List (Gate N)) := by
  intro g hg
  simp at hg

theorem unitaryGates_append_iff {c d : List (Gate N)} :
    UnitaryGates (c ++ d) ↔ UnitaryGates c ∧ UnitaryGates d := by
  constructor
  · intro h
    exact ⟨fun g hg => h g (List.mem_append.2 (Or.inl hg)),
      fun g hg => h g (List.mem_append.2 (Or.inr hg))⟩
  · rintro ⟨hc, hd⟩ g hg
    rcases List.mem_append.1 hg with h | h
    · exact hc g h
    · exact hd g h

theorem unitaryGates_append {c d : List (Gate N)} (hc : UnitaryGates c) (hd : UnitaryGates d) :
    UnitaryGates (c ++ d) := unitaryGates_append_iff.2 ⟨hc, hd⟩

theorem unitaryGates_singleton_one (q : Fin N) {m : Matrix Bool Bool ℂ}
    (hm : m ∈ Matrix.unitaryGroup Bool ℂ) : UnitaryGates [Gate.one q m] := by
  intro g hg q' m' hgm
  rw [List.mem_singleton] at hg
  rw [hg] at hgm
  injection hgm with h1 h2
  rw [← h2]
  exact hm

theorem unitaryGates_singleton_cx (c t : Fin N) (h : c ≠ t) : UnitaryGates [Gate.cx c t h] := by
  intro g hg q' m' hgm
  rw [List.mem_singleton] at hg
  rw [hg] at hgm
  cases hgm

theorem unitaryGates_cons_cx (c t : Fin N) (h : c ≠ t) {l : List (Gate N)}
    (hl : UnitaryGates l) : UnitaryGates (Gate.cx c t h :: l) :=
  unitaryGates_append (unitaryGates_singleton_cx c t h) hl

theorem unitaryGates_cons_one (q : Fin N) {m : Matrix Bool Bool ℂ}
    (hm : m ∈ Matrix.unitaryGroup Bool ℂ) {l : List (Gate N)} (hl : UnitaryGates l) :
    UnitaryGates (Gate.one q m :: l) :=
  unitaryGates_append (unitaryGates_singleton_one q hm) hl

theorem tr_append {c d : List (Gate N)} {t r t' r' : ℕ} (hc : TR c t r) (hd : TR d t' r') :
    TR (c ++ d) (t + t') (r + r') := by
  induction hc with
  | nil => simpa using hd
  | cx a b h _ ih => exact TR.cx a b h ih
  | exact q hg _ ih =>
    have h := TR.exact q hg ih
    rw [Nat.add_right_comm] at h
    exact h
  | rot q φ _ ih =>
    have h := TR.rot q φ ih
    rw [Nat.add_right_comm] at h
    exact h

/-- `TR` with the two counts replaced by equal ones. -/
theorem TR.congr {c : List (Gate N)} {t r t' r' : ℕ} (h : TR c t r) (ht : t = t')
    (hr : r = r') : TR c t' r' := by
  subst ht
  subst hr
  exact h

end Free
