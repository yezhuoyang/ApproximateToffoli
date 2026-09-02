import ApproxToffoli.BlockCutU

/-!
# The angle budget: where `2 − √2` comes from

Let `N = trC X` for an 8×8 unitary `X`, and let `σ₁ … σ₄` be the singular values of
`N/2` (all in `[0,1]`, because `N = X⁰⁰ + X¹¹` is a sum of two contractions).  Write

    σ_k = cos (ψ_k / 2),   ψ_k ∈ [0, π],

so that `σ_k` is the cosine of the `k`-th **principal angle** `θ_k = ψ_k/2` between
`S₀ = ℂ⁴_AB ⊗ |Φ⟩_Cs` and `(X ⊗ 1) S₀`, and

    ‖N‖²_HS = ∑ 4 cos²(ψ_k/2) = ∑ |1 + e^{i ψ_k}|² = 8 + 2 ∑ cos ψ_k.

`ψ_k` is exactly the **relative phase, in the k-th principal direction, of the two
diagonal C-blocks `X⁰⁰` and `X¹¹` of `X`** — the "two terms" of the compromise.

The single remaining analytic input is the **BUDGET**

    Ψ(X) = ∑_k ψ_k ≥ π,

i.e. the total phase that a rank-one reflection puts across the AB|C cut is at least
`π` and cannot be redistributed away by the two BC crossings.  (Numerically:
min Ψ = π exactly, attained both at `X = CCZ`, where `ψ = (0,0,0,π)`, and at the free
maximiser, where `ψ = (π/4,π/4,π/4,π/4)`.  For an even-rank reflection the budget is
`0` and the ceiling `16` is reached.)

Everything below is the *elementary* half: BUDGET ⟹ `‖N‖²_HS ≤ 8 + 4√2`.  The constant
`√2` enters as `4 cos(π/4)`: spreading a total phase of `π` equally over the four
principal directions.  Equality forces all four angles to be `π/4`.
-/

open Real Set Matrix

namespace AngleBudget

noncomputable def GG (y : ℝ) : ℝ := Real.cos y + (Real.sqrt 2 / 2) * y

private lemma ghas (x : ℝ) : HasDerivAt GG (-Real.sin x + Real.sqrt 2 / 2) x := by
  have h1 : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
  have h2 : HasDerivAt (fun y : ℝ => (Real.sqrt 2 / 2) * y) (Real.sqrt 2 / 2) x := by
    simpa using (hasDerivAt_id x).const_mul (Real.sqrt 2 / 2)
  exact h1.add h2

private lemma gderiv (x : ℝ) : deriv GG x = -Real.sin x + Real.sqrt 2 / 2 := (ghas x).deriv

private lemma gcont : Continuous GG := Real.continuous_cos.add (continuous_const.mul continuous_id)

private lemma sin_lt1 {x : ℝ} (h0 : 0 < x) (h1 : x < π / 4) : Real.sin x < Real.sqrt 2 / 2 := by
  have hp := Real.pi_pos
  rw [← Real.sin_pi_div_four]
  exact Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h1

private lemma sin_lt2 {x : ℝ} (h0 : 3 * π / 4 < x) (h1 : x < π) : Real.sin x < Real.sqrt 2 / 2 := by
  have hp := Real.pi_pos
  rw [← Real.sin_pi_sub x, ← Real.sin_pi_div_four]
  exact Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)

private lemma sin_gt {x : ℝ} (h0 : π / 4 < x) (h1 : x < 3 * π / 4) :
    Real.sqrt 2 / 2 < Real.sin x := by
  have hp := Real.pi_pos
  have h2 : Real.sqrt 2 / 2 < 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  rcases lt_trichotomy x (π / 2) with h | h | h
  · rw [← Real.sin_pi_div_four]
    exact Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h0
  · rw [h, Real.sin_pi_div_two]; exact h2
  · rw [← Real.sin_pi_sub x, ← Real.sin_pi_div_four]
    exact Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)

private lemma gmono1 : StrictMonoOn GG (Icc 0 (π / 4)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) gcont.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [gderiv]
  have := sin_lt1 hx.1 hx.2
  linarith

private lemma ganti : StrictAntiOn GG (Icc (π / 4) (3 * π / 4)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) gcont.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [gderiv]
  have := sin_gt hx.1 hx.2
  linarith

private lemma gmono2 : StrictMonoOn GG (Icc (3 * π / 4) π) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) gcont.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [gderiv]
  have := sin_lt2 hx.1 hx.2
  linarith

private lemma GG_pi_div_four : GG (π / 4) = Real.sqrt 2 / 2 * (1 + π / 4) := by
  simp [GG, Real.cos_pi_div_four]; ring

/-- The one non-monotone comparison: `GG π < GG (π/4)`, i.e. `3π/4 < 1 + √2`
    (`2.3562 < 2.4142`).  This is the only place where a numeric fact about `π` and
    `√2` is used. -/
private lemma GG_pi_lt : GG π < GG (π / 4) := by
  rw [GG_pi_div_four]
  simp only [GG, Real.cos_pi]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, Real.pi_lt_d2,
    Real.pi_gt_d2]

/-! ## The tangent-line inequality at `π/4` -/

/-- **Tangent line at `π/4`.**  `cos x ≤ cos(π/4) − sin(π/4)·(x − π/4)` for
    `x ∈ [0, π]`.  Note `cos` is *not* concave on `[0,π]`, so this is not Jensen:
    on `[3π/4, π]` the function `cos x + (√2/2)x` increases again, and the inequality
    survives only because `3π/4 < 1 + √2`. -/
theorem cos_le_tangent {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π) :
    Real.cos x ≤ Real.sqrt 2 / 2 * (1 + π / 4 - x) := by
  have hp := Real.pi_pos
  have key : GG x ≤ GG (π / 4) := by
    rcases le_total x (π / 4) with h | h
    · exact gmono1.monotoneOn ⟨h0, h⟩ ⟨by linarith, le_refl _⟩ h
    · rcases le_total x (3 * π / 4) with h' | h'
      · exact ganti.antitoneOn ⟨le_refl _, by linarith⟩ ⟨h, h'⟩ h
      · exact le_trans (gmono2.monotoneOn ⟨h', h1⟩ ⟨by linarith, le_refl _⟩ h1) GG_pi_lt.le
  rw [GG_pi_div_four] at key
  simp only [GG] at key
  have e : Real.sqrt 2 / 2 * (1 + π / 4 - x)
      = Real.sqrt 2 / 2 * (1 + π / 4) - Real.sqrt 2 / 2 * x := by ring
  rw [e]; linarith

/-- The strict form: equality in `cos_le_tangent` holds only at `x = π/4`. -/
theorem cos_lt_tangent {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π) (hne : x ≠ π / 4) :
    Real.cos x < Real.sqrt 2 / 2 * (1 + π / 4 - x) := by
  have hp := Real.pi_pos
  have key : GG x < GG (π / 4) := by
    rcases lt_trichotomy x (π / 4) with h | h | h
    · exact gmono1 ⟨h0, h.le⟩ ⟨by linarith, le_refl _⟩ h
    · exact absurd h hne
    · rcases le_total x (3 * π / 4) with h' | h'
      · exact ganti ⟨le_refl _, by linarith⟩ ⟨h.le, h'⟩ h
      · exact lt_of_le_of_lt (gmono2.monotoneOn ⟨h', h1⟩ ⟨by linarith, le_refl _⟩ h1) GG_pi_lt
  rw [GG_pi_div_four] at key
  simp only [GG] at key
  have e : Real.sqrt 2 / 2 * (1 + π / 4 - x)
      = Real.sqrt 2 / 2 * (1 + π / 4) - Real.sqrt 2 / 2 * x := by ring
  rw [e]; linarith

/-! ## The four-angle budget -/

/-- **The budget inequality.**  Four angles in `[0, π]` whose sum is at least `π`
    have `∑ cos ψ_k ≤ 4 cos(π/4) = 2√2`.  This is the sole source of `√2`. -/
theorem cos_sum_le (ψ : Fin 4 → ℝ) (h0 : ∀ k, 0 ≤ ψ k) (h1 : ∀ k, ψ k ≤ π)
    (hb : π ≤ ∑ k, ψ k) : ∑ k, Real.cos (ψ k) ≤ 2 * Real.sqrt 2 := by
  calc ∑ k, Real.cos (ψ k)
      ≤ ∑ k, Real.sqrt 2 / 2 * (1 + π / 4 - ψ k) :=
        Finset.sum_le_sum fun k _ => cos_le_tangent (h0 k) (h1 k)
    _ = Real.sqrt 2 / 2 * ((4 : ℝ) + π - ∑ k, ψ k) := by
        simp only [Fin.sum_univ_four]; ring
    _ ≤ Real.sqrt 2 / 2 * (4 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 2 * Real.sqrt 2 := by ring

/-- **BUDGET ⟹ the HS bound.**  With `σ_k = cos(ψ_k/2)` the squared singular values of
    `N/2` are `cos²(ψ_k/2) = (2 + 2cos ψ_k)/4`, so `‖N‖²_HS = ∑ (2 + 2 cos ψ_k)`. -/
theorem budget_bound (ψ : Fin 4 → ℝ) (h0 : ∀ k, 0 ≤ ψ k) (h1 : ∀ k, ψ k ≤ π)
    (hb : π ≤ ∑ k, ψ k) : ∑ k, (2 + 2 * Real.cos (ψ k)) ≤ 8 + 4 * Real.sqrt 2 := by
  have h := cos_sum_le ψ h0 h1 hb
  simp only [Fin.sum_univ_four] at h ⊢
  linarith

/-- **Equality forces the flat configuration.**  This answers the sharpness question:
    `∑ sin² θ_k ≥ 2 − √2` with equality *only* when all four principal angles are
    equal to `π/8`. -/
theorem budget_eq_flat (ψ : Fin 4 → ℝ) (h0 : ∀ k, 0 ≤ ψ k) (h1 : ∀ k, ψ k ≤ π)
    (hb : π ≤ ∑ k, ψ k) (heq : ∑ k, (2 + 2 * Real.cos (ψ k)) = 8 + 4 * Real.sqrt 2) :
    ∀ k, ψ k = π / 4 := by
  by_contra hc
  push_neg at hc
  obtain ⟨j, hj⟩ := hc
  have hstrict : ∑ k, Real.cos (ψ k) < 2 * Real.sqrt 2 := by
    calc ∑ k, Real.cos (ψ k)
        < ∑ k, Real.sqrt 2 / 2 * (1 + π / 4 - ψ k) := by
          refine Finset.sum_lt_sum (fun k _ => cos_le_tangent (h0 k) (h1 k))
            ⟨j, Finset.mem_univ j, cos_lt_tangent (h0 j) (h1 j) hj⟩
      _ = Real.sqrt 2 / 2 * ((4 : ℝ) + π - ∑ k, ψ k) := by
          simp only [Fin.sum_univ_four]; ring
      _ ≤ Real.sqrt 2 / 2 * (4 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
      _ = 2 * Real.sqrt 2 := by ring
  simp only [Fin.sum_univ_four] at heq hstrict
  linarith

/-! ## Route (ii): the `∑ sin² θ_k ≥ 2 − √2` form -/

/-- **The principal-angle form.**  Four principal angles in `[0, π/2]` with total at
    least `π/2` satisfy `∑ sin² θ_k ≥ 2 − √2 = 4 sin²(π/8)`. -/
theorem sin_sq_sum_ge (θ : Fin 4 → ℝ) (h0 : ∀ k, 0 ≤ θ k) (h1 : ∀ k, θ k ≤ π / 2)
    (hb : π / 2 ≤ ∑ k, θ k) : 2 - Real.sqrt 2 ≤ ∑ k, Real.sin (θ k) ^ 2 := by
  have hp := Real.pi_pos
  have h := cos_sum_le (fun k => 2 * θ k) (fun k => by linarith [h0 k])
    (fun k => by linarith [h1 k]) (by simp only [Fin.sum_univ_four] at hb ⊢; linarith)
  have hc : ∀ k, Real.cos (2 * θ k) = 1 - 2 * Real.sin (θ k) ^ 2 := fun k => by
    rw [Real.cos_two_mul', Real.cos_sq']; ring
  simp only [hc, Fin.sum_univ_four] at h
  simp only [Fin.sum_univ_four]
  linarith

/-- `2 − √2 = 4 sin²(π/8)`, the constant in closed form. -/
theorem two_sub_sqrt_two : 2 - Real.sqrt 2 = 4 * Real.sin (π / 8) ^ 2 := by
  have h : Real.sin (π / 8) ^ 2 = (1 - Real.cos (π / 4)) / 2 := by
    have e : π / 4 = 2 * (π / 8) := by ring
    rw [e, Real.cos_two_mul', Real.cos_sq']
    ring
  rw [h, Real.cos_pi_div_four]
  ring

/-! ## The bridge to `BlockU.HSSmall` -/

/-- The same reduction stated at trace level only (no spectral hypothesis): any
    representation of `‖N‖²_HS` as `∑ (2 + 2 cos ψ_k)` with the `ψ_k` obeying the
    budget already gives `HSSmall`. -/
theorem hsSmall_of_budget_trace {N : Mat4} (ψ : Fin 4 → ℝ)
    (h0 : ∀ k, 0 ≤ ψ k) (h1 : ∀ k, ψ k ≤ π) (hb : π ≤ ∑ k, ψ k)
    (htr : RCLike.re (Matrix.trace (Nᴴ * N)) = ∑ k, (2 + 2 * Real.cos (ψ k))) :
    BlockU.HSSmall N := by
  change RCLike.re (Matrix.trace (Nᴴ * N)) ≤ 8 + 4 * Real.sqrt 2
  rw [htr]
  exact budget_bound ψ h0 h1 hb

/-- **BUDGET ⟹ `HSSmall`.**  `Nᴴ N` is Hermitian with eigenvalues `4 cos²(ψ_k/2) =
    2 + 2 cos ψ_k`; the budget on the `ψ_k` gives `‖N‖²_HS ≤ 8 + 4√2` outright. -/
theorem hsSmall_of_budget {N : Mat4} (hH : (Nᴴ * N).IsHermitian) (ψ : Fin 4 → ℝ)
    (h0 : ∀ k, 0 ≤ ψ k) (h1 : ∀ k, ψ k ≤ π) (hb : π ≤ ∑ k, ψ k)
    (hspec : ∀ k, hH.eigenvalues k = 2 + 2 * Real.cos (ψ k)) :
    BlockU.HSSmall N := by
  refine hsSmall_of_budget_trace ψ h0 h1 hb ?_
  rw [hH.trace_eq_sum_eigenvalues]
  simp only [map_sum, hspec]
  push_cast
  simp [Complex.cos_ofReal_re]

end AngleBudget

#print axioms AngleBudget.cos_le_tangent
#print axioms AngleBudget.cos_sum_le
#print axioms AngleBudget.budget_bound
#print axioms AngleBudget.budget_eq_flat
#print axioms AngleBudget.sin_sq_sum_ge
#print axioms AngleBudget.two_sub_sqrt_two
#print axioms AngleBudget.hsSmall_of_budget
#print axioms AngleBudget.hsSmall_of_budget_trace
