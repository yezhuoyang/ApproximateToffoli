/-
  ApproxToffoli.CPauliSplit

  The two exact identities behind THEOREM 3 of `notes/OFFSLICE_REDUCTION.md` §1½.

  For a block unitary `Z = [[N₀, X], [Y, N₁]]` (blocks w.r.t. the C qubit) put the
  two *C-Pauli components*

      Z₀ := (N₀ + N₁)/2 = ½ tr_C(Z),      Z_z := (N₀ - N₁)/2 = ½ tr_C(Z·(1⊗σ_z)).

  Then

    (1)  Herm(N₀ᴴ N₁) = Z₀ᴴ Z₀ - Z_zᴴ Z_z        -- a DIFFERENCE OF GRAM MATRICES
    (2)  ‖Z₀‖_F² + ‖Z_z‖_F² = (‖N₀‖_F² + ‖N₁‖_F²)/2

  (1) holds because the cross terms `Z_zᴴZ₀ - Z₀ᴴZ_z` are anti-Hermitian and die in
  `Herm(·)`; (2) is the parallelogram law.  Together with unitarity of `Z` (which gives
  `‖N₀‖_F² + ‖N₁‖_F² = 8 - Δ`) they turn

      Ψ := 2 tr H - 4 λ_min(H) - Δ        (H := Herm(N₀ᴴN₁),  Δ := ‖X‖_F² + ‖Y‖_F²)

  into `Ψ = 8 - 2Δ - 4 tr(Z_zᴴZ_z) - 4 λ_min(Z₀ᴴZ₀ - Z_zᴴZ_z)`, after which ONE Weyl
  inequality `λ_min(A-B) ≥ λ_min(A) - λ_max(B)` yields THEOREM 3.

  Everything below is stated division-free (multiplied through by the obvious power of
  two) so that no field inverses appear.  The eigenvalue half of THEOREM 3 is NOT
  formalised here — only its algebraic core, which is the part that is stable.
-/

import ApproxToffoli.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

open Matrix

-- every result here is pure matrix algebra; `n` needs no decidable equality
set_option linter.unusedSectionVars false

noncomputable section

namespace CPauliSplit

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The C-Pauli components -/

/-- Twice the `σ₀` (average) component: `N₀ + N₁`.  Kept unhalved to stay division-free. -/
def twoZ0 (N₀ N₁ : Matrix n n ℂ) : Matrix n n ℂ := N₀ + N₁

/-- Twice the `σ_z` (difference) component: `N₀ - N₁`. -/
def twoZz (N₀ N₁ : Matrix n n ℂ) : Matrix n n ℂ := N₀ - N₁

/-- Twice the Hermitian part of `M`. -/
def twoHerm (M : Matrix n n ℂ) : Matrix n n ℂ := M + Mᴴ

/-! ## Identity (1): the Hermitian part is a difference of Gram matrices -/

/-- **The Gram identity.**  `(N₀+N₁)ᴴ(N₀+N₁) - (N₀-N₁)ᴴ(N₀-N₁) = 2·Herm(N₀ᴴN₁)`,
i.e. after halving, `Herm(N₀ᴴN₁) = Z₀ᴴZ₀ - Z_zᴴZ_z`.

This is the identity that makes the whole `C`-Pauli split work: it exhibits the
Hermitian part `H` as a *difference of two positive semidefinite Gram matrices*, so that
a single Weyl inequality controls `λ_min(H)`. -/
theorem gram_identity (N₀ N₁ : Matrix n n ℂ) :
    (twoZ0 N₀ N₁)ᴴ * (twoZ0 N₀ N₁) - (twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁)
      = twoHerm (N₀ᴴ * N₁) + twoHerm (N₀ᴴ * N₁) := by
  simp only [twoZ0, twoZz, twoHerm, conjTranspose_add, conjTranspose_sub,
    conjTranspose_mul, conjTranspose_conjTranspose]
  noncomm_ring

/-- The cross terms really are anti-Hermitian — the reason (1) holds. -/
theorem cross_antiHerm (N₀ N₁ : Matrix n n ℂ) :
    ((twoZz N₀ N₁)ᴴ * (twoZ0 N₀ N₁) - (twoZ0 N₀ N₁)ᴴ * (twoZz N₀ N₁))
      + ((twoZz N₀ N₁)ᴴ * (twoZ0 N₀ N₁) - (twoZ0 N₀ N₁)ᴴ * (twoZz N₀ N₁))ᴴ = 0 := by
  simp only [twoZ0, twoZz, conjTranspose_add, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_conjTranspose]
  noncomm_ring

/-! ## Identity (2): the parallelogram law -/

/-- **The norm identity.**  `‖N₀+N₁‖_F² + ‖N₀-N₁‖_F² = 2‖N₀‖_F² + 2‖N₁‖_F²`, i.e. after
halving, `‖Z₀‖_F² + ‖Z_z‖_F² = (‖N₀‖_F² + ‖N₁‖_F²)/2`. -/
theorem frob_parallelogram (N₀ N₁ : Matrix n n ℂ) :
    trace ((twoZ0 N₀ N₁)ᴴ * (twoZ0 N₀ N₁)) + trace ((twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁))
      = (trace (N₀ᴴ * N₀) + trace (N₀ᴴ * N₀))
        + (trace (N₁ᴴ * N₁) + trace (N₁ᴴ * N₁)) := by
  have h : (twoZ0 N₀ N₁)ᴴ * (twoZ0 N₀ N₁) + (twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁)
      = (N₀ᴴ * N₀ + N₀ᴴ * N₀) + (N₁ᴴ * N₁ + N₁ᴴ * N₁) := by
    simp only [twoZ0, twoZz, conjTranspose_add, conjTranspose_sub]
    noncomm_ring
  calc trace ((twoZ0 N₀ N₁)ᴴ * (twoZ0 N₀ N₁)) + trace ((twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁))
      = trace ((twoZ0 N₀ N₁)ᴴ * (twoZ0 N₀ N₁) + (twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁)) := by
        rw [trace_add]
    _ = trace ((N₀ᴴ * N₀ + N₀ᴴ * N₀) + (N₁ᴴ * N₁ + N₁ᴴ * N₁)) := by rw [h]
    _ = _ := by rw [trace_add, trace_add, trace_add]

/-! ## The pointwise form — no eigenvalues anywhere

The Rayleigh quotient of `H` splits as a difference of two squared norms.  This is what
lets the whole reduction be stated without ever invoking spectral theory. -/

/-- **Pointwise Gram identity.**  For every vector `v`,
`⟪v, 2·(2 Herm(N₀ᴴN₁)) v⟫ = ‖(N₀+N₁)v‖² - ‖(N₀-N₁)v‖²`, in the division-free form
`star v ⬝ᵥ ((twoZ0ᴴ twoZ0 - twoZzᴴ twoZz) *ᵥ v) = ...`. -/
theorem rayleigh_split (N₀ N₁ : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ ((twoHerm (N₀ᴴ * N₁) + twoHerm (N₀ᴴ * N₁)) *ᵥ v)
      = star v ⬝ᵥ (((twoZ0 N₀ N₁)ᴴ * (twoZ0 N₀ N₁)) *ᵥ v)
        - star v ⬝ᵥ (((twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁)) *ᵥ v) := by
  rw [← gram_identity, sub_mulVec, dotProduct_sub]

/-- Recovery: the two `C`-Pauli components determine the blocks. -/
theorem blocks_of_components (N₀ N₁ : Matrix n n ℂ) :
    twoZ0 N₀ N₁ + twoZz N₀ N₁ = N₀ + N₀ ∧ twoZ0 N₀ N₁ - twoZz N₀ N₁ = N₁ + N₁ := by
  constructor <;> · simp only [twoZ0, twoZz]; abel



/-! ## The reflection dictionary

`(D)` is stated with a rank-one reflection `S_v = 1 - 2vv^*`.  The lemmas below eliminate it,
turning `(D)` into the pointwise form of `(F)` with **no eigenvalues anywhere**.  Everything is
kept division-free, so `S_v` appears as `rankOneRefl v = 1 - P - P` with `P = vv^*`. -/

section Reflection

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one projection `v v^*`. -/
def rankOneProj (v : n → ℂ) : Matrix n n ℂ := vecMulVec v (star v)

/-- The rank-one reflection `1 - 2vv^*`, written division-free. -/
def rankOneRefl (v : n → ℂ) : Matrix n n ℂ := 1 - rankOneProj v - rankOneProj v

lemma rankOneProj_conjTranspose (v : n → ℂ) : (rankOneProj v)ᴴ = rankOneProj v := by
  ext i j
  simp [rankOneProj, vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

lemma trace_mul_rankOneProj (M : Matrix n n ℂ) (v : n → ℂ) :
    trace (M * rankOneProj v) = star v ⬝ᵥ (M *ᵥ v) := by
  simp only [trace, diag_apply, Matrix.mul_apply, rankOneProj, vecMulVec_apply,
    dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma rankOneProj_mul_self (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    rankOneProj v * rankOneProj v = rankOneProj v := by
  have h : ∑ k, star (v k) * v k = 1 := by
    simpa [dotProduct, Pi.star_apply] using hv
  ext i j
  simp only [rankOneProj, Matrix.mul_apply, vecMulVec_apply, Pi.star_apply]
  calc ∑ k, v i * star (v k) * (v k * star (v j))
      = (v i * star (v j)) * ∑ k, star (v k) * v k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = v i * star (v j) := by rw [h, mul_one]

lemma rankOneRefl_conjTranspose (v : n → ℂ) : (rankOneRefl v)ᴴ = rankOneRefl v := by
  simp [rankOneRefl, rankOneProj_conjTranspose]

lemma rankOneRefl_mul_self (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    rankOneRefl v * rankOneRefl v = 1 := by
  simp only [rankOneRefl, sub_mul, mul_sub, one_mul, mul_one, rankOneProj_mul_self v hv]
  abel

/-- **The reflection dictionary.**  With `S := 1 - 2vv^*` and `‖v‖ = 1`,

  `‖N₁ - N₀S‖_F² = ‖N₀‖_F² + ‖N₁‖_F² - tr(2Herm(N₀ᴴN₁)) + 2·⟪v, 2Herm(N₀ᴴN₁) v⟫`.

Combined with `gram_identity` and `rayleigh_split` this expresses `(D)` entirely in the
`C`-Pauli components `Z₀, Z_z`, with no eigenvalues. -/
theorem refl_expand (N₀ N₁ : Matrix n n ℂ) (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    trace ((N₁ - N₀ * rankOneRefl v)ᴴ * (N₁ - N₀ * rankOneRefl v))
      = trace (N₀ᴴ * N₀) + trace (N₁ᴴ * N₁)
        - trace (twoHerm (N₀ᴴ * N₁))
        + (star v ⬝ᵥ (twoHerm (N₀ᴴ * N₁) *ᵥ v) + star v ⬝ᵥ (twoHerm (N₀ᴴ * N₁) *ᵥ v)) := by
  have hS : (rankOneRefl v)ᴴ = rankOneRefl v := rankOneRefl_conjTranspose v
  have hSS : rankOneRefl v * rankOneRefl v = 1 := rankOneRefl_mul_self v hv
  have hexp : (N₁ - N₀ * rankOneRefl v)ᴴ * (N₁ - N₀ * rankOneRefl v)
      = N₁ᴴ * N₁ - N₁ᴴ * N₀ * rankOneRefl v - rankOneRefl v * (N₀ᴴ * N₁)
        + rankOneRefl v * (N₀ᴴ * N₀) * rankOneRefl v := by
    simp only [conjTranspose_sub, conjTranspose_mul, hS]
    noncomm_ring
  rw [hexp]
  have h1 : trace (rankOneRefl v * (N₀ᴴ * N₀) * rankOneRefl v) = trace (N₀ᴴ * N₀) := by
    rw [Matrix.trace_mul_comm (rankOneRefl v * (N₀ᴴ * N₀)) (rankOneRefl v),
      ← Matrix.mul_assoc, hSS, Matrix.one_mul]
  have h3 : trace (rankOneRefl v * (N₀ᴴ * N₁)) = trace (N₀ᴴ * N₁ * rankOneRefl v) :=
    Matrix.trace_mul_comm _ _
  have hsum : N₁ᴴ * N₀ * rankOneRefl v + N₀ᴴ * N₁ * rankOneRefl v
      = twoHerm (N₀ᴴ * N₁) * rankOneRefl v := by
    simp only [twoHerm, conjTranspose_mul, conjTranspose_conjTranspose, add_mul]
    abel
  have hfin : trace (twoHerm (N₀ᴴ * N₁) * rankOneRefl v)
      = trace (twoHerm (N₀ᴴ * N₁))
        - (star v ⬝ᵥ (twoHerm (N₀ᴴ * N₁) *ᵥ v) + star v ⬝ᵥ (twoHerm (N₀ᴴ * N₁) *ᵥ v)) := by
    simp only [rankOneRefl, mul_sub, mul_one, trace_sub, trace_mul_rankOneProj]
    ring
  have hkey : trace (N₁ᴴ * N₀ * rankOneRefl v) + trace (N₀ᴴ * N₁ * rankOneRefl v)
      = trace (twoHerm (N₀ᴴ * N₁))
        - (star v ⬝ᵥ (twoHerm (N₀ᴴ * N₁) *ᵥ v) + star v ⬝ᵥ (twoHerm (N₀ᴴ * N₁) *ᵥ v)) := by
    rw [← trace_add, hsum, hfin]
  simp only [trace_add, trace_sub, h1, h3]
  linear_combination -hkey

/-- ⭐ **The capstone identity.**  For any `N₀, N₁` and any unit vector `v`, with
`S := 1 - 2vv^*`, `Z₀' := N₀+N₁`, `Z_z' := N₀-N₁`:

  `‖N₁ - N₀S‖_F² = ‖Z_z'‖_F² + ‖Z₀'v‖² - ‖Z_z'v‖²`.

Halving (`Z₀' = 2Z₀`, `Z_z' = 2Z_z`) this is `‖N₁-N₀S_v‖_F² = 4‖Z_z‖_F² + 4‖Z₀v‖² - 4‖Z_zv‖²`,
which is the dictionary of `notes/THE_ONE_INEQUALITY.md` turning `(D)` into the pointwise form of
`(F)`.  **No unitarity of `Z` and no eigenvalues are used** — only `‖v‖ = 1`. -/
theorem refl_capstone (N₀ N₁ : Matrix n n ℂ) (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    trace ((N₁ - N₀ * rankOneRefl v)ᴴ * (N₁ - N₀ * rankOneRefl v))
      = trace ((twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁))
        + star v ⬝ᵥ (((twoZ0 N₀ N₁)ᴴ * (twoZ0 N₀ N₁)) *ᵥ v)
        - star v ⬝ᵥ (((twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁)) *ᵥ v) := by
  have hE := refl_expand N₀ N₁ v hv
  have hG := gram_identity N₀ N₁
  have hP := frob_parallelogram N₀ N₁
  have hT : trace ((twoZ0 N₀ N₁)ᴴ * (twoZ0 N₀ N₁)) - trace ((twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁))
      = trace (twoHerm (N₀ᴴ * N₁)) + trace (twoHerm (N₀ᴴ * N₁)) := by
    rw [← trace_sub, hG, trace_add]
  have hRR : star v ⬝ᵥ (twoHerm (N₀ᴴ * N₁) *ᵥ v) + star v ⬝ᵥ (twoHerm (N₀ᴴ * N₁) *ᵥ v)
      = star v ⬝ᵥ (((twoZ0 N₀ N₁)ᴴ * (twoZ0 N₀ N₁)) *ᵥ v)
        - star v ⬝ᵥ (((twoZz N₀ N₁)ᴴ * (twoZz N₀ N₁)) *ᵥ v) := by
    rw [← rayleigh_split, add_mulVec, dotProduct_add]
  rw [hE]
  linear_combination -hP / 2 + hT / 2 + hRR

end Reflection

end CPauliSplit
