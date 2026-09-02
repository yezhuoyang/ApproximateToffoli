-- Compiled with lean_run_code against Mathlib (no ApproxToffoli imports needed).
-- Diagnostics: {"success":true,"timed_out":false,"diagnostics":[]}   (0 errors, 0 warnings)
-- #print axioms GeoCert.claimG_second_order        -> [propext, Classical.choice, Quot.sound]
-- #print axioms GeoCert.claimG_second_order_sharp  -> [propext, Classical.choice, Quot.sound]
-- #print axioms GeoCert.abs_trace_herm_mul_unitary_le -> [propext, Classical.choice, Quot.sound]
-- Saved at scratchpad/GeoCert.lean
import Mathlib

/-!
# CLAIM (G) at first and second order: a nuclear-norm dual certificate

`L(Y) = ∑_k |arg λ_k(Y)| = ‖log Y‖_*` is the geodesic distance from `Y` to `1` for the
bi-invariant Finsler metric on `U(8)` given by the nuclear norm.  With
`K₁ = U(4)_AB ⊗ 1_C`, `K₂ = 1_A ⊗ U(4)_BC` and `W₅ = K₁K₂K₁K₂K₁` (five alternating
neighbour gates), CLAIM (G) is exactly

    dist_*(CCZ, W₅) ≥ π ,

i.e. **no five-neighbour-gate circuit is nuclear-closer to `CCZ` than the empty
circuit** — `L(CCZ) = π` exactly, `CCZ` having eigenphases `0,…,0,π`.  (Verified
numerically: `min_{Z∈W₅} L(Z·CCZ) = π` to `3·10⁻¹⁵`, attained both at `Z = 1` and on a
positive-dimensional manifold where the eight eigenphases are `±π/8`, four each.)

This file proves the *linearised* statements — the exact first- and second-order shadows
of CLAIM (G) at the equality point `Z = 1`.  Write

    Θ(CCZ) = -i log CCZ = π e₇e₇ᴴ   (`e₇ = |111⟩`),
    k₁ = Herm(4) ⊗ 1_C ,   k₂ = 1_A ⊗ Herm(4)  (the two local subalgebras).

Lie data (all computed exactly, `scratchpad/geoG2.py`): `dim k₁ = dim k₂ = 16`,
`k₁ ∩ k₂ = 1_A ⊗ u(2)_B ⊗ 1_C` (dim 4), `dim (k₁+k₂) = 28`,
`dim (k₁+k₂+[k₁,k₂]) = 55`, and **all twelve principal angles between
`k₁ ⊖ (k₁∩k₂)` and `k₂ ⊖ (k₁∩k₂)` equal `π/2`** — the two subalgebras are orthogonal
modulo their intersection.  In the Pauli basis
`(k₁+k₂)^⊥ = span{σ_a⊗σ_b⊗σ_c : a≠0, c≠0}` (dim 36) and
`(k₁+k₂+[k₁,k₂])^⊥ = span{σ_a⊗1_B⊗σ_c : a,c≠0}` (dim 9).

The tangent cone of `W₅` at `1` contains `k₁+k₂` (first order) and, through commutators
`e^{sX}e^{sY}e^{-sX}e^{-sY} = exp(s²[X,Y]+…)`, also `[k₁,k₂]` (second order).

MAIN THEOREM (`claimG_second_order`).  For every `S ∈ k₁ + k₂ + [k₁,k₂]`,
`‖Θ(CCZ) - S‖_* ≥ π = ‖Θ(CCZ)‖_*`: the origin is a nuclear-norm best approximation of
`Θ(CCZ)` from that 55-dimensional space.  So no first- or second-order deformation of the
trivial circuit gains anything on it.

The certificate is the Pauli string `F₂ = Z_A ⊗ 1_B ⊗ Z_C`: `‖F₂‖_op = 1`,
`⟨111|F₂|111⟩ = 1`, `F₂ ⊥ k₁+k₂+[k₁,k₂]`.  For the four-letter form of the claim, whose
target is a Householder `H_w = 1 - 2ww^H` about an arbitrary product vector `w = q⊗|1⟩`,
the certificate is instead `F₁ = -Z_A⊗Z_B⊗Z_C` (`⟨w|F₁|w⟩ = 1` for every `q` in the
`|00⟩,|11⟩` plane, hence after a local `U_A⊗U_B` for every `q`); `F₁ ⊥ k₁+k₂` only.  No
`F` in the 9-dimensional space works for an entangled `q` (the AC-Schmidt vectors of `w`
force `F = 1_A⊗(-Z_C)`, whose partial trace over A is `-2Z_C ≠ 0`), which is why the
`CCZ` form of the claim is the one to attack.

A single fixed `F` cannot prove the *global* claim: `tr(F Θ(Z·CCZ))` ranges over
`[-5.6, +6.7]` on the family for both `F₁` and `F₂` (`scratchpad/geoG2.py`), and at each
of the spread minimisers the certificate is forced to be `sign Θ`, which varies over the
minimiser manifold (`scratchpad/geoG4.py`).

Indexing throughout: `Fin 8 ∋ i = 4a + 2b + c`, with `a`,`b`,`c` the A-, B-, C-bits.
-/

open Matrix Finset
open scoped ComplexOrder

namespace GeoCert

set_option linter.style.longLine false

/-! ## 1.  The nuclear norm of a Hermitian matrix and its duality bound -/

/-- Nuclear (trace, Schatten-1) norm of a Hermitian matrix: the sum of the absolute
values of its eigenvalues.  For `Θ = -i log Y` with `Y` unitary this is exactly
`L(Y) = ∑_k |arg λ_k(Y)|`, the nuclear-norm Finsler distance from `Y` to `1`. -/
noncomputable def nuc {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℂ}
    (hT : T.IsHermitian) : ℝ := ∑ i, |hT.eigenvalues i|

lemma trace_diagonal_mul {n : Type*} [Fintype n] [DecidableEq n] (g : n → ℂ)
    (A : Matrix n n ℂ) : (diagonal g * A).trace = ∑ i, g i * A i i := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq]

lemma trace_mul_diag {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (d : n → ℂ) :
    (A * diagonal d).trace = ∑ i, A i i * d i := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq']

/-- **Nuclear-norm duality (Hermitian case)** — the only analytic ingredient, and the
primitive that `SharpBounds.lean` and `HS2Core.lean` record as missing from Mathlib.
If `F` is unitary (in particular if `F` is a Hermitian involution, so `‖F‖_op = 1`) then
`|tr (F T)| ≤ ‖T‖_*` for every Hermitian `T`. -/
theorem abs_trace_mul_le_nuc {n : Type*} [Fintype n] [DecidableEq n] {F T : Matrix n n ℂ}
    (hF : F ∈ Matrix.unitaryGroup n ℂ) (hT : T.IsHermitian) :
    ‖(F * T).trace‖ ≤ nuc hT := by
  set U : Matrix n n ℂ := (hT.eigenvectorUnitary : Matrix n n ℂ) with hU
  set d : n → ℂ := (RCLike.ofReal ∘ hT.eigenvalues) with hd
  have hUu : U ∈ Matrix.unitaryGroup n ℂ := (hT.eigenvectorUnitary).2
  have hsp : T = U * diagonal d * (star U) := by simpa [hU, hd] using hT.spectral_theorem
  have hV : (star U * F * U) ∈ Matrix.unitaryGroup n ℂ :=
    mul_mem (mul_mem (Unitary.star_mem hUu) hF) hUu
  have htr : (F * T).trace = ((star U * F * U) * diagonal d).trace := by
    have h1 : F * T = (F * U * diagonal d) * (star U) := by rw [hsp]; noncomm_ring
    rw [h1, Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  rw [htr, trace_mul_diag, nuc]
  calc ‖∑ i, (star U * F * U) i i * d i‖
      ≤ ∑ i, ‖(star U * F * U) i i * d i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |hT.eigenvalues i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        have h1 : ‖(star U * F * U) i i‖ ≤ 1 := entry_norm_bound_of_unitary hV i i
        have h2 : ‖d i‖ = |hT.eigenvalues i| := by simp [hd]
        rw [h2]
        nlinarith [abs_nonneg (hT.eigenvalues i), norm_nonneg ((star U * F * U) i i)]

/-- The shape the rest of this project asks for: `|Tr (A N)| ≤ ‖A‖_*` for `N` unitary
and `A` Hermitian. -/
theorem abs_trace_herm_mul_unitary_le {n : Type*} [Fintype n] [DecidableEq n]
    {A N : Matrix n n ℂ} (hA : A.IsHermitian) (hN : N ∈ Matrix.unitaryGroup n ℂ) :
    ‖(A * N).trace‖ ≤ nuc hA := by
  rw [Matrix.trace_mul_comm]; exact abs_trace_mul_le_nuc hN hA

/-- Turn a certificate into a lower bound on the nuclear norm. -/
theorem le_nuc_of_certificate {n : Type*} [Fintype n] [DecidableEq n] {F T : Matrix n n ℂ}
    {c : ℝ} (hF : F ∈ Matrix.unitaryGroup n ℂ) (hT : T.IsHermitian)
    (hc : (F * T).trace = (c : ℂ)) (hc0 : 0 ≤ c) : c ≤ nuc hT := by
  have h := abs_trace_mul_le_nuc hF hT
  rwa [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0] at h

/-! ## 2.  The two local subalgebras -/

/-- `M ⊗ 1_C`: `M` acts on the AB pair, the identity on C. -/
def kronAB (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if (i : ℕ) % 2 = (j : ℕ) % 2 then M ⟨i / 2, by omega⟩ ⟨j / 2, by omega⟩ else 0

/-- `1_A ⊗ W`: `W` acts on the BC pair, the identity on A. -/
def kronBC (W : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if (i : ℕ) / 4 = (j : ℕ) / 4 then W ⟨i % 4, by omega⟩ ⟨j % 4, by omega⟩ else 0

lemma kronAB_apply_of_ne (M : Matrix (Fin 4) (Fin 4) ℂ) {i j : Fin 8}
    (h : (i : ℕ) % 2 ≠ (j : ℕ) % 2) : kronAB M i j = 0 := by simp [kronAB, h]

lemma kronBC_apply_of_ne (W : Matrix (Fin 4) (Fin 4) ℂ) {i j : Fin 8}
    (h : (i : ℕ) / 4 ≠ (j : ℕ) / 4) : kronBC W i j = 0 := by simp [kronBC, h]

/-! ## 3.  The certificates -/

/-- `F₁ = -Z_A ⊗ Z_B ⊗ Z_C`, minus the parity operator. -/
def gF1 : Fin 8 → ℂ := ![-1, 1, 1, -1, 1, -1, -1, 1]
/-- `F₂ = Z_A ⊗ 1_B ⊗ Z_C`. -/
def gF2 : Fin 8 → ℂ := ![1, -1, 1, -1, -1, 1, -1, 1]

/-- `Z_A ⊗ 1_B ⊗ 1_C`. -/
def zA : Matrix (Fin 8) (Fin 8) ℂ := diagonal fun i => if (i : ℕ) / 4 = 0 then 1 else -1
/-- `1_A ⊗ 1_B ⊗ Z_C`. -/
def zC : Matrix (Fin 8) (Fin 8) ℂ := diagonal fun i => if (i : ℕ) % 2 = 0 then 1 else -1

private lemma diag_unitary (g : Fin 8 → ℂ) (h : ∀ i, g i * star (g i) = 1) :
    (diagonal g) ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star (diagonal g) = diagonal (star g) := by
    simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  rw [hs, Matrix.diagonal_mul_diagonal,
    show (fun i => g i * star g i) = (fun _ : Fin 8 => (1 : ℂ)) from funext h]
  exact Matrix.diagonal_one

lemma F1_unitary : (diagonal gF1) ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  diag_unitary _ fun i => by fin_cases i <;> simp [gF1]

lemma F2_unitary : (diagonal gF2) ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  diag_unitary _ fun i => by fin_cases i <;> simp [gF2]

/-- `F₁ ⊥ k₁`: the two C-partners of each AB basis state carry opposite parity. -/
lemma F1_kronAB (M : Matrix (Fin 4) (Fin 4) ℂ) : (diagonal gF1 * kronAB M).trace = 0 := by
  rw [trace_diagonal_mul]; simp [kronAB, gF1, Fin.sum_univ_eight]

/-- `F₁ ⊥ k₂`. -/
lemma F1_kronBC (W : Matrix (Fin 4) (Fin 4) ℂ) : (diagonal gF1 * kronBC W).trace = 0 := by
  rw [trace_diagonal_mul]; simp [kronBC, gF1, Fin.sum_univ_eight]; ring

/-- `F₂ ⊥ k₁`. -/
lemma F2_kronAB (M : Matrix (Fin 4) (Fin 4) ℂ) : (diagonal gF2 * kronAB M).trace = 0 := by
  rw [trace_diagonal_mul]; simp [kronAB, gF2, Fin.sum_univ_eight]

/-- `F₂ ⊥ k₂`. -/
lemma F2_kronBC (W : Matrix (Fin 4) (Fin 4) ℂ) : (diagonal gF2 * kronBC W).trace = 0 := by
  rw [trace_diagonal_mul]; simp [kronBC, gF2, Fin.sum_univ_eight]; ring

lemma F2_eq : diagonal gF2 = zA * zC := by
  rw [zA, zC, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i; fin_cases i <;> norm_num [gF2]

/-- `1_A⊗1_B⊗Z_C` commutes with everything AB-local. -/
lemma zC_comm_kronAB (M : Matrix (Fin 4) (Fin 4) ℂ) : zC * kronAB M = kronAB M * zC := by
  ext i j
  rw [zC, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : (i : ℕ) % 2 = (j : ℕ) % 2
  · rw [h]; ring
  · rw [kronAB_apply_of_ne M h]; ring

/-- `Z_A⊗1_B⊗1_C` commutes with everything BC-local. -/
lemma zA_comm_kronBC (W : Matrix (Fin 4) (Fin 4) ℂ) : zA * kronBC W = kronBC W * zA := by
  ext i j
  rw [zA, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : (i : ℕ) / 4 = (j : ℕ) / 4
  · rw [h]; ring
  · rw [kronBC_apply_of_ne W h]; ring

lemma zA_comm_zC : zA * zC = zC * zA := by
  rw [zA, zC, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; ring

/-- **`F₂ ⊥ [k₁,k₂]`**, the second-order orthogonality.  `F₂ = z_A z_C` with `z_C`
central for `k₁` and `z_A` central for `k₂`, so the two traces agree by cyclicity. -/
lemma F2_trace_comm (M W : Matrix (Fin 4) (Fin 4) ℂ) :
    (diagonal gF2 * (kronAB M * kronBC W - kronBC W * kronAB M)).trace = 0 := by
  have h1 : diagonal gF2 * (kronAB M * kronBC W) = (zA * kronAB M) * (zC * kronBC W) := by
    rw [F2_eq, show zA * zC * (kronAB M * kronBC W) = zA * (zC * kronAB M) * kronBC W by
      noncomm_ring, zC_comm_kronAB]
    noncomm_ring
  have h2 : diagonal gF2 * (kronBC W * kronAB M) = (zC * kronBC W) * (zA * kronAB M) := by
    rw [F2_eq, zA_comm_zC,
      show zC * zA * (kronBC W * kronAB M) = zC * (zA * kronBC W) * kronAB M by noncomm_ring,
      zA_comm_kronBC]
    noncomm_ring
  rw [Matrix.mul_sub, Matrix.trace_sub, h1, h2, Matrix.trace_mul_comm]
  ring

/-! ## 4.  The target `Θ(CCZ) = π |111⟩⟨111|` -/

/-- `Θ(CCZ) = -i log CCZ = π e₇e₇ᴴ`. -/
noncomputable def cczLog : Matrix (Fin 8) (Fin 8) ℂ :=
  diagonal fun i => if i = 7 then (Real.pi : ℂ) else 0

lemma F1_cczLog : (diagonal gF1 * cczLog).trace = (Real.pi : ℂ) := by
  rw [trace_diagonal_mul]; simp [cczLog, gF1]

lemma F2_cczLog : (diagonal gF2 * cczLog).trace = (Real.pi : ℂ) := by
  rw [trace_diagonal_mul]; simp [cczLog, gF2]

/-- `‖Θ(CCZ)‖_* = π`, i.e. `L(CCZ) = π`: the bound below is attained at `S = 0`. -/
theorem nuc_cczLog (hT : cczLog.IsHermitian) : nuc hT = Real.pi := by
  have hps : cczLog.PosSemidef := by
    rw [show cczLog = diagonal (fun i : Fin 8 => if i = 7 then (Real.pi : ℂ) else 0) from rfl,
      Matrix.posSemidef_diagonal_iff]
    intro i
    by_cases h : i = 7
    · simpa [h] using Complex.zero_le_real.2 Real.pi_nonneg
    · simp [h]
  have hnn : ∀ i, 0 ≤ hT.eigenvalues i := fun i => hps.eigenvalues_nonneg i
  have htr : cczLog.trace = ((Real.pi : ℝ) : ℂ) := by simp [cczLog, Matrix.trace_diagonal]
  have hsum : ((∑ i, hT.eigenvalues i : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) := by
    rw [← htr, hT.trace_eq_sum_eigenvalues]; push_cast; rfl
  have hfin : (∑ i, hT.eigenvalues i) = Real.pi := by exact_mod_cast hsum
  rw [nuc, show (∑ i, |hT.eigenvalues i|) = ∑ i, hT.eigenvalues i from
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hnn i)]
  exact hfin

/-! ## 5.  The theorems -/

/-- **CLAIM (G), first order.**  `‖Θ(CCZ) - M⊗1_C - 1_A⊗W‖_* ≥ π` for all `M, W`, i.e.
`0` is a nuclear-norm best approximation of `Θ(CCZ)` from `k₁ + k₂`.
Certificate: `F₂ = Z_A⊗1_B⊗Z_C`. -/
theorem claimG_first_order {T : Matrix (Fin 8) (Fin 8) ℂ} (hT : T.IsHermitian)
    (M W : Matrix (Fin 4) (Fin 4) ℂ) (hTdef : T = cczLog - kronAB M - kronBC W) :
    Real.pi ≤ nuc hT := by
  refine le_nuc_of_certificate F2_unitary hT ?_ Real.pi_nonneg
  rw [hTdef, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
    F2_cczLog, F2_kronAB, F2_kronBC]
  ring

/-- Same, with the certificate `F₁ = -Z_A⊗Z_B⊗Z_C` — the one that also handles a
Householder about an entangled product vector `q ⊗ |1⟩`. -/
theorem claimG_first_order' {T : Matrix (Fin 8) (Fin 8) ℂ} (hT : T.IsHermitian)
    (M W : Matrix (Fin 4) (Fin 4) ℂ) (hTdef : T = cczLog - kronAB M - kronBC W) :
    Real.pi ≤ nuc hT := by
  refine le_nuc_of_certificate F1_unitary hT ?_ Real.pi_nonneg
  rw [hTdef, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
    F1_cczLog, F1_kronAB, F1_kronBC]
  ring

/-- Membership in the 55-dimensional space `k₁ + k₂ + [k₁,k₂]`. -/
def InTangent2 (S : Matrix (Fin 8) (Fin 8) ℂ) : Prop :=
  ∃ (M W : Matrix (Fin 4) (Fin 4) ℂ) (r : ℕ) (c : Fin r → ℂ)
    (M' W' : Fin r → Matrix (Fin 4) (Fin 4) ℂ),
    S = kronAB M + kronBC W +
      ∑ k, c k • (kronAB (M' k) * kronBC (W' k) - kronBC (W' k) * kronAB (M' k))

lemma F2_orth_tangent2 {S : Matrix (Fin 8) (Fin 8) ℂ} (hS : InTangent2 S) :
    (diagonal gF2 * S).trace = 0 := by
  obtain ⟨M, W, r, c, M', W', rfl⟩ := hS
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
    F2_kronAB, F2_kronBC, Matrix.mul_sum, Matrix.trace_sum]
  simp [F2_trace_comm]

/-- **CLAIM (G), second order.**  `0` is a nuclear-norm best approximation of `Θ(CCZ)`
from the 55-dimensional space `k₁ + k₂ + [k₁,k₂]`, which contains every first- and
second-order deformation of the trivial five-gate circuit. -/
theorem claimG_second_order {T S : Matrix (Fin 8) (Fin 8) ℂ} (hT : T.IsHermitian)
    (hS : InTangent2 S) (hTdef : T = cczLog - S) : Real.pi ≤ nuc hT := by
  refine le_nuc_of_certificate F2_unitary hT ?_ Real.pi_nonneg
  rw [hTdef, Matrix.mul_sub, Matrix.trace_sub, F2_cczLog, F2_orth_tangent2 hS]
  ring

/-- The bound is sharp: `dist_*(Θ(CCZ), k₁+k₂+[k₁,k₂]) = π` exactly. -/
theorem claimG_second_order_sharp (hT : cczLog.IsHermitian) :
    nuc hT = Real.pi ∧
    ∀ (S T : Matrix (Fin 8) (Fin 8) ℂ) (hT' : T.IsHermitian), InTangent2 S → T = cczLog - S →
      Real.pi ≤ nuc hT' :=
  ⟨nuc_cczLog hT, fun _ _ hT' hS hTd => claimG_second_order hT' hS hTd⟩

end GeoCert