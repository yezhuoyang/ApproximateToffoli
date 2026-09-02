import Mathlib
import ApproxToffoli.BlockFree
open Real Finset

namespace AngleSum

lemma sin_add_cos_ge_one {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ π / 2) :
    1 ≤ Real.sin v + Real.cos v := by
  have hs : 0 ≤ Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
  have hc : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc ⟨by linarith, h1⟩
  nlinarith [Real.sin_sq_add_cos_sq v, mul_nonneg hs hc]

lemma one_sub_cos_ge {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ π / 2) :
    v - Real.sin v ≤ 1 - Real.cos v := by
  set f : ℝ → ℝ := fun x => 1 - Real.cos x - x + Real.sin x with hf
  have hcont : ContinuousOn f (Set.Icc 0 (π / 2)) := by
    apply ContinuousOn.add
    · exact (continuousOn_const.sub (Real.continuous_cos.continuousOn)).sub continuousOn_id
    · exact Real.continuous_sin.continuousOn
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc 0 (π / 2))) := by
    apply DifferentiableOn.add
    · exact ((differentiableOn_const 1).sub Real.differentiable_cos.differentiableOn).sub
        differentiableOn_id
    · exact Real.differentiable_sin.differentiableOn
  have hderiv : ∀ x, deriv f x = Real.sin x - 1 + Real.cos x := by
    intro x; simp [hf, Real.deriv_cos, Real.deriv_sin]
  have hmono : MonotoneOn f (Set.Icc 0 (π / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2)) hcont hdiff ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [hderiv]
    have := sin_add_cos_ge_one (le_of_lt hx.1) (le_of_lt hx.2)
    linarith
  have := hmono ⟨le_refl 0, by positivity⟩ ⟨h0, h1⟩ h0
  simp [hf] at this
  linarith

lemma cos_add_sin_le {u : ℝ} (h0 : -(π / 4) ≤ u) (h1 : u ≤ π / 4) :
    Real.cos u + Real.sin u ≤ 1 + u := by
  by_cases hu : 0 ≤ u
  · linarith [Real.sin_le hu, Real.cos_le_one u]
  · push_neg at hu
    have := one_sub_cos_ge (v := -u) (by linarith) (by linarith [pi_pos])
    rw [Real.cos_neg, Real.sin_neg] at this
    linarith

/-- Tangent line to `sin` at `π/4` on `[0, π/2]`. -/
lemma sin_le_tangent {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ π / 2) :
    Real.sin m ≤ Real.sqrt 2 / 2 * (1 + m - π / 4) := by
  have e1 : m - π / 4 + π / 4 = m := by ring
  have h := Real.sin_add (m - π / 4) (π / 4)
  rw [e1, Real.sin_pi_div_four, Real.cos_pi_div_four] at h
  have hb := cos_add_sin_le (u := m - π / 4) (by linarith) (by linarith)
  rw [h]
  nlinarith [hb, Real.sqrt_nonneg 2]

/-- `√2 sin e ≥ e + π/4 - 1` on `[-π/2, π/2]`, EQUALITY at `e = -π/4`. -/
lemma sqrt2_sin_ge {e : ℝ} (h0 : -(π / 2) ≤ e) (h1 : e ≤ π / 2) :
    e + π / 4 - 1 ≤ Real.sqrt 2 * Real.sin e := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : (0:ℝ) < Real.sqrt 2 := by positivity
  by_cases he : e ≤ 0
  · have ht := sin_le_tangent (m := -e) (by linarith) (by linarith)
    rw [Real.sin_neg] at ht
    nlinarith [ht, hs2, hs2pos]
  · push_neg at he
    have hs2lb : (1.414 : ℝ) < Real.sqrt 2 := by nlinarith [hs2, hs2pos]
    have hpi : π < 3.15 := pi_lt_d2
    have hpi0 : (0:ℝ) < π := pi_pos
    have hj : 2 / π * e ≤ Real.sin e := Real.mul_le_sin (le_of_lt he) h1
    have hj' : 2 * e ≤ π * Real.sin e := by
      calc 2 * e = π * (2 / π * e) := by field_simp
        _ ≤ π * Real.sin e := mul_le_mul_of_nonneg_left hj (le_of_lt hpi0)
    nlinarith [hj', hs2, hs2pos, hs2lb, hpi, hpi0, he, h1,
      mul_nonneg (le_of_lt hs2pos)
        (Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt he) (by linarith))]

/-- Tangent line to `cos` at `π/4`, valid on all of `[0, π]`. -/
lemma sqrt2_cos_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π) :
    Real.sqrt 2 * Real.cos x ≤ 1 + π / 4 - x := by
  have he := sqrt2_sin_ge (e := x - π / 2) (by linarith) (by linarith)
  have hc : Real.cos x = -Real.sin (x - π / 2) := by
    rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  rw [hc]; nlinarith [he]

/-- Tangent line to `sin²` at `π/8`, valid on all of `[0, π/2]`; equality at `π/8`.
    `1/2 - √2/4 = sin²(π/8)` and the slope is `sin(π/4) = √2/2`.  Note `sin²` is
    convex only on `[0, π/4]`, so this is NOT plain Jensen. -/
lemma sin_sq_tangent {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) :
    (1 / 2 - Real.sqrt 2 / 4) + Real.sqrt 2 / 2 * (θ - π / 8) ≤ Real.sin θ ^ 2 := by
  have hg := sqrt2_cos_le (x := 2 * θ) (by linarith) (by linarith)
  have hpyth := Real.sin_sq_add_cos_sq θ
  have hd : Real.sin θ ^ 2 = (1 - Real.cos (2 * θ)) / 2 := by
    rw [Real.cos_two_mul']; linarith
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : (0:ℝ) < Real.sqrt 2 := by positivity
  rw [hd]; nlinarith [hg, hs2, hs2pos]

/-- **ANGLESUM ⟹ HS2 (the Jensen half).**  If the four singular values
    `s k ∈ [0,2]` of `Tr_C X` have principal angles `arccos (s k / 2)` summing
    to at least `π/2`, then `‖Tr_C X‖²_F = ∑ s k ^ 2 ≤ 8 + 4√2`.  Equality
    exactly when all four angles are `π/8`, i.e. all `s k = 2cos(π/8)` — which
    is what the numerical maximiser satisfies (all four singular values equal
    1.8477590650 = 2cos(π/8)). -/
theorem sq_sum_le_of_angle_sum {s : Fin 4 → ℝ} (h0 : ∀ k, 0 ≤ s k) (h2 : ∀ k, s k ≤ 2)
    (hsum : π / 2 ≤ ∑ k, Real.arccos (s k / 2)) :
    ∑ k, (s k) ^ 2 ≤ 8 + 4 * Real.sqrt 2 := by
  set θ : Fin 4 → ℝ := fun k => Real.arccos (s k / 2) with hθ
  have hb1 : ∀ k, s k / 2 ≤ 1 := fun k => by linarith [h2 k]
  have hb2 : ∀ k, (-1 : ℝ) ≤ s k / 2 := fun k => by linarith [h0 k]
  have hθ0 : ∀ k, 0 ≤ θ k := fun k => Real.arccos_nonneg _
  have hθ1 : ∀ k, θ k ≤ π / 2 := fun k =>
    Real.arccos_le_pi_div_two.2 (by linarith [h0 k])
  have hcos : ∀ k, Real.cos (θ k) = s k / 2 := fun k => Real.cos_arccos (hb2 k) (hb1 k)
  have hsq : ∀ k, (s k) ^ 2 = 4 - 4 * Real.sin (θ k) ^ 2 := by
    intro k
    have := Real.sin_sq_add_cos_sq (θ k)
    rw [hcos k] at this
    nlinarith [this]
  have htan : ∀ k, (1 / 2 - Real.sqrt 2 / 4) + Real.sqrt 2 / 2 * (θ k - π / 8)
      ≤ Real.sin (θ k) ^ 2 := fun k => sin_sq_tangent (hθ0 k) (hθ1 k)
  have hsumtan : (2 - Real.sqrt 2) + Real.sqrt 2 / 2 * ((∑ k, θ k) - π / 2)
      ≤ ∑ k, Real.sin (θ k) ^ 2 := by
    have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => htan k)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib] at this
    calc (2 - Real.sqrt 2) + Real.sqrt 2 / 2 * ((∑ k, θ k) - π / 2)
        = (4 : ℝ) * (1 / 2 - Real.sqrt 2 / 4)
            + Real.sqrt 2 / 2 * ((∑ k, θ k) - 4 * (π / 8)) := by ring
      _ ≤ ∑ k, Real.sin (θ k) ^ 2 := by linarith [this]
  have hgain : (2 : ℝ) - Real.sqrt 2 ≤ ∑ k, Real.sin (θ k) ^ 2 := by
    have hs2pos : (0:ℝ) < Real.sqrt 2 := by positivity
    nlinarith [hsumtan, hsum, hs2pos]
  calc ∑ k, (s k) ^ 2 = ∑ k, (4 - 4 * Real.sin (θ k) ^ 2) := by
        exact Finset.sum_congr rfl fun k _ => hsq k
    _ = 16 - 4 * ∑ k, Real.sin (θ k) ^ 2 := by
        simp [Finset.sum_sub_distrib, Finset.mul_sum]; norm_num
    _ ≤ 8 + 4 * Real.sqrt 2 := by linarith [hgain]

end AngleSum

/-
=============================================================================
FILE 2 — the simplified equivalent of HS2.  Saved at
  C:\Users\yezhu\AppData\Local\Temp\claude\c--Users-yezhu-Documents-ApproximateToffoli\5e27a5cf-3a5d-4198-9eed-65587f254419\scratchpad\BlockClean.lean

COMPILED via lean_run_code against the BUILT tree.  Two runs, diagnostics
quoted verbatim, both:  {"success":true,"timed_out":false,"diagnostics":[]}
  run 1: Pi4, Pi4_conjTranspose, Pi4_mul_self, Pi4_trace, E77_eq_kronABC,
         IsRank1Proj4, isRank1Proj4_conj, HS2clean, HS2_of_HS2clean
  run 2: refl_unitary, clean_cfg_unitary

HS2clean is HS2 with M0 and M2 FUSED into one unitary G and the reflection
turned into a free rank-one projection on the AB factor:
  4 unitaries (64 real params)  ->  3 unitaries + 1 rank-one AB projection (54).
It sits strictly between HS2 and BlockFree.HSFree (62 params):
  HSFree  ==>  HS2clean  ==>  HS2 .
Numerically HS2clean is still exactly tight: 13.656854249492, gap 6.22e-15.
=============================================================================
-/

open Matrix Complex

noncomputable section

namespace BlockClean

/-! `Π₄ = |11⟩⟨11|`, the AB-half of the CCZ reflection vector. -/
def Pi4 : Mat4 := Matrix.of fun i j => if i = 3 ∧ j = 3 then (1 : ℂ) else 0

lemma Pi4_conjTranspose : Pi4ᴴ = Pi4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pi4, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma Pi4_mul_self : Pi4 * Pi4 = Pi4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pi4, Matrix.mul_apply, Matrix.of_apply]

lemma Pi4_trace : Matrix.trace Pi4 = 1 := by
  simp [Pi4, Matrix.trace, Matrix.diag_apply, Matrix.of_apply]

/-- `E₇₇ = Π₄ ⊗ |1⟩⟨1|`: the CCZ reflection vector IS a product across AB|C. -/
lemma E77_eq_kronABC : BlockFree.E77 = kronABC Pi4 proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BlockFree.E77, Pi4, proj1, kronABC, Matrix.of_apply]

/-- `Q` is a rank-one orthogonal projection on `Mat4`. -/
def IsRank1Proj4 (Q : Mat4) : Prop := Qᴴ = Q ∧ Q * Q = Q ∧ Matrix.trace Q = 1

lemma isRank1Proj4_conj {M : Mat4} (hM : M * Mᴴ = 1) : IsRank1Proj4 (Mᴴ * Pi4 * M) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Pi4_conjTranspose, Matrix.mul_assoc]
  · calc Mᴴ * Pi4 * M * (Mᴴ * Pi4 * M)
        = Mᴴ * Pi4 * (M * Mᴴ) * Pi4 * M := by noncomm_ring
      _ = Mᴴ * (Pi4 * Pi4) * M := by rw [hM, Matrix.mul_one]; noncomm_ring
      _ = Mᴴ * Pi4 * M := by rw [Pi4_mul_self]
  · calc Matrix.trace (Mᴴ * Pi4 * M)
        = Matrix.trace (Mᴴ * (Pi4 * M)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (Pi4 * M * Mᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace Pi4 := by rw [Matrix.mul_assoc, hM, Matrix.mul_one]
      _ = 1 := Pi4_trace

/-- **(HS2CLEAN)** — `HS2` with `M₀, M₂` fused into `G` and the reflection freed
    to an arbitrary rank-one projection `Q` on the AB factor. -/
def HS2clean : Prop := ∀ (G W1 W2 Q : Mat4), IsUnitary4 G → IsUnitary4 W1 → IsUnitary4 W2 →
    IsRank1Proj4 Q →
    BlockU.HSSmall (BlockU.trC (embedBC W2 * kronABC G 1 *
      (1 - kronABC Q proj1 - kronABC Q proj1) * embedBC W1))

/-- **`HS2clean → HS2`.**  Reparametrisation `G = M₂M₀`, `Q = M₀ᴴ Π₄ M₀`; this is
    a bijection onto the pairs `(G, Q)`, so the two are in fact equivalent (the
    converse needs only "every rank-one projection is unitarily `Π₄`"). -/
theorem HS2_of_HS2clean (h : HS2clean) : BlockU.HS2 := by
  intro M0 M2 W1 W2 hM0 hM2 hW1 hW2
  have hM0' : M0 * M0ᴴ = 1 := mul_eq_one_comm.mp hM0
  set Q : Mat4 := M0ᴴ * Pi4 * M0 with hQdef
  have hQ : IsRank1Proj4 Q := isRank1Proj4_conj hM0'
  have hccz : CCZ8 = 1 - kronABC Pi4 proj1 - kronABC Pi4 proj1 := by
    rw [BlockFree.ccz8_eq_refl, E77_eq_kronABC]
  have hPi : kronABC M2 1 * kronABC Pi4 proj1 * kronABC M0 1
      = kronABC (M2 * Pi4 * M0) proj1 := by
    rw [kronABC_mul, kronABC_mul]; simp
  have hG : kronABC (M2 * M0) 1 * kronABC Q proj1 = kronABC (M2 * M0 * Q) proj1 := by
    rw [kronABC_mul]; simp
  have hQeq : M2 * M0 * Q = M2 * Pi4 * M0 := by
    rw [hQdef]
    calc M2 * M0 * (M0ᴴ * Pi4 * M0) = M2 * (M0 * M0ᴴ) * Pi4 * M0 := by noncomm_ring
      _ = M2 * Pi4 * M0 := by rw [hM0', Matrix.mul_one]
  have key : kronABC M2 1 * CCZ8 * kronABC M0 1
      = kronABC (M2 * M0) 1 * (1 - kronABC Q proj1 - kronABC Q proj1) := by
    calc kronABC M2 1 * CCZ8 * kronABC M0 1
        = kronABC M2 1 * (1 - kronABC Pi4 proj1 - kronABC Pi4 proj1) * kronABC M0 1 := by
          rw [hccz]
      _ = kronABC M2 1 * kronABC M0 1
            - kronABC M2 1 * kronABC Pi4 proj1 * kronABC M0 1
            - kronABC M2 1 * kronABC Pi4 proj1 * kronABC M0 1 := by noncomm_ring
      _ = kronABC (M2 * M0) 1 - kronABC (M2 * Pi4 * M0) proj1
            - kronABC (M2 * Pi4 * M0) proj1 := by
          rw [hPi, kronABC_mul]; simp
      _ = kronABC (M2 * M0) 1 - kronABC (M2 * M0 * Q) proj1
            - kronABC (M2 * M0 * Q) proj1 := by rw [hQeq]
      _ = kronABC (M2 * M0) 1 * (1 - kronABC Q proj1 - kronABC Q proj1) := by
          rw [← hG]; noncomm_ring
  have e : embedBC W2 * kronABC M2 1 * CCZ8 * kronABC M0 1 * embedBC W1
      = embedBC W2 * (kronABC M2 1 * CCZ8 * kronABC M0 1) * embedBC W1 := by noncomm_ring
  rw [e, key]
  have e2 : embedBC W2 * (kronABC (M2 * M0) 1 * (1 - kronABC Q proj1 - kronABC Q proj1))
        * embedBC W1
      = embedBC W2 * kronABC (M2 * M0) 1 * (1 - kronABC Q proj1 - kronABC Q proj1)
        * embedBC W1 := by noncomm_ring
  rw [e2]
  exact h (M2 * M0) W1 W2 Q (isUnitary4_mul hM2 hM0) hW1 hW2 hQ

/-! ## Unitarity of the clean configuration — needed to use the DISTANCE form of
`HS2clean` via the already-compiled `PauliHS.hsSmall_iff_pauli`. -/

lemma refl_unitary {Q : Mat4} (hQ : IsRank1Proj4 Q) :
    (1 - kronABC Q proj1 - kronABC Q proj1)ᴴ *
      (1 - kronABC Q proj1 - kronABC Q proj1) = (1 : Mat8) := by
  obtain ⟨hh, hi, -⟩ := hQ
  have hR : (kronABC Q proj1)ᴴ = kronABC Q proj1 := by
    rw [PauliHS.kronABC_conjTranspose, hh, proj1_conjTranspose]
  have hR2 : kronABC Q proj1 * kronABC Q proj1 = kronABC Q proj1 := by
    rw [kronABC_mul, hi, proj1_sq]
  have hcT : (1 - kronABC Q proj1 - kronABC Q proj1)ᴴ
      = 1 - kronABC Q proj1 - kronABC Q proj1 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hR]
  rw [hcT]
  calc (1 - kronABC Q proj1 - kronABC Q proj1) * (1 - kronABC Q proj1 - kronABC Q proj1)
      = 1 - kronABC Q proj1 - kronABC Q proj1 - kronABC Q proj1 - kronABC Q proj1
          + kronABC Q proj1 * kronABC Q proj1 + kronABC Q proj1 * kronABC Q proj1
          + kronABC Q proj1 * kronABC Q proj1 + kronABC Q proj1 * kronABC Q proj1 := by
        noncomm_ring
    _ = (1 : Mat8) := by rw [hR2]; abel

lemma clean_cfg_unitary {G W1 W2 Q : Mat4} (hG : IsUnitary4 G) (hW1 : IsUnitary4 W1)
    (hW2 : IsUnitary4 W2) (hQ : IsRank1Proj4 Q) :
    (embedBC W2 * kronABC G 1 * (1 - kronABC Q proj1 - kronABC Q proj1) * embedBC W1)ᴴ *
      (embedBC W2 * kronABC G 1 * (1 - kronABC Q proj1 - kronABC Q proj1) * embedBC W1)
      = (1 : Mat8) :=
  PauliHS.mul_left_unitary
    (PauliHS.mul_left_unitary
      (PauliHS.mul_left_unitary (embedBC_unitary W2 hW2) (PauliHS.kronABC_one_unitary hG))
      (refl_unitary hQ))
    (embedBC_unitary W1 hW1)

end BlockClean