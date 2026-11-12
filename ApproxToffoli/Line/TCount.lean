/-
T-gate and rotation counts of circuits on a line: the bookkeeping.

`TRle c T R` says that the one-qubit gates of `c` split into Clifford+T gates with at
most `T` T gates and at most `R` rotations.  It is closed under append and under
`invCirc`, CNOTs are free, a Clifford+T gate of cost `m` adds `m`, a phase gate of
arbitrary angle adds one rotation.
-/
import Mathlib
import ApproxToffoli.Line.TGates

namespace Line

open Matrix ExactLine

variable {N : ℕ}

theorem tr_append {c d : List (Gate N)} {t r t' r' : ℕ} (hc : TR c t r) (hd : TR d t' r') :
    TR (c ++ d) (t + t') (r + r') := by
  induction hc with
  | nil => simpa using hd
  | cx a b adj _ ih => exact TR.cx a b adj ih
  | exact q hg _ ih =>
    have h := TR.exact q hg ih
    rw [Nat.add_right_comm] at h
    exact h
  | rot q φ _ ih =>
    have h := TR.rot q φ ih
    rw [Nat.add_right_comm] at h
    exact h

theorem tr_invCirc {c : List (Gate N)} {t r : ℕ} (hc : TR c t r) : TR (invCirc c) t r := by
  induction hc with
  | nil => exact TR.nil
  | cx a b adj _ ih =>
    rw [invCirc_cons]
    exact tr_append ih (TR.cx a b adj TR.nil)
  | exact q hg _ ih =>
    rw [invCirc_cons]
    have h := tr_append ih (TR.exact q (tcost_conjTranspose hg) TR.nil)
    simpa using h
  | rot q φ _ ih =>
    rw [invCirc_cons]
    have h := tr_append ih (TR.rot q (-φ) TR.nil)
    rw [← conjTranspose_pGate] at h
    simpa using h

/-- At most `T` T gates and at most `R` rotations. -/
def TRle (c : List (Gate N)) (T R : ℕ) : Prop := ∃ t r, TR c t r ∧ t ≤ T ∧ r ≤ R

theorem trle_mono {c : List (Gate N)} {T R T' R' : ℕ} (h : TRle c T R) (hT : T ≤ T')
    (hR : R ≤ R') : TRle c T' R' := by
  obtain ⟨t, r, h, h1, h2⟩ := h
  exact ⟨t, r, h, h1.trans hT, h2.trans hR⟩

theorem trle_nil : TRle ([] : List (Gate N)) 0 0 := ⟨0, 0, TR.nil, le_rfl, le_rfl⟩

theorem trle_append {c d : List (Gate N)} {T R T' R' : ℕ} (hc : TRle c T R)
    (hd : TRle d T' R') : TRle (c ++ d) (T + T') (R + R') := by
  obtain ⟨t, r, h, h1, h2⟩ := hc
  obtain ⟨t', r', h', h1', h2'⟩ := hd
  exact ⟨t + t', r + r', tr_append h h', Nat.add_le_add h1 h1', Nat.add_le_add h2 h2'⟩

theorem trle_invCirc {c : List (Gate N)} {T R : ℕ} (hc : TRle c T R) :
    TRle (invCirc c) T R := by
  obtain ⟨t, r, h, h1, h2⟩ := hc
  exact ⟨t, r, tr_invCirc h, h1, h2⟩

theorem trle_cx {c : List (Gate N)} {T R : ℕ} (a b : Fin N)
    (adj : a.val + 1 = b.val ∨ b.val + 1 = a.val) (hc : TRle c T R) :
    TRle (Gate.cx a b adj :: c) T R := by
  obtain ⟨t, r, h, h1, h2⟩ := hc
  exact ⟨t, r, TR.cx a b adj h, h1, h2⟩

theorem trle_one {c : List (Gate N)} {T R : ℕ} (q : Fin N) {g : Matrix Bool Bool ℂ} {m : ℕ}
    (hg : TCost g m) (hc : TRle c T R) : TRle (Gate.one q g :: c) (T + m) R := by
  obtain ⟨t, r, h, h1, h2⟩ := hc
  exact ⟨t + m, r, TR.exact q hg h, Nat.add_le_add_right h1 m, h2⟩

theorem trle_rot {c : List (Gate N)} {T R : ℕ} (q : Fin N) (φ : ℝ) (hc : TRle c T R) :
    TRle (Gate.one q (pGate φ) :: c) T (R + 1) := by
  obtain ⟨t, r, h, h1, h2⟩ := hc
  exact ⟨t, r + 1, TR.rot q φ h, h1, Nat.add_le_add_right h2 1⟩

theorem trle_h {c : List (Gate N)} {T R : ℕ} (q : Fin N) (hc : TRle c T R) :
    TRle (Gate.one q hGate :: c) T R := trle_one q TCost.h hc

theorem trle_x {c : List (Gate N)} {T R : ℕ} (q : Fin N) (hc : TRle c T R) :
    TRle (Gate.one q xGate :: c) T R := trle_one q tcost_xGate hc

end Line
