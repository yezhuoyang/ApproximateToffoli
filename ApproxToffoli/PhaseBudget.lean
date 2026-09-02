import ApproxToffoli.AngleBudget

/-!
# `PhaseBudget` — two exact obstructions behind `Ψ(X) ≥ π`

`Ψ(X) = ∑_k ψ_k`, `ψ_k = 2 arccos σ_k`, `σ_k = sv_k(trC X / 2)`.

* §A  the **odd-multiple-of-π** obstruction.  If `V ∈ U(n)` has all its eigenvalue
  multiplicities even and `R = 1 - 2ww^H` is a hyperplane reflection, then each
  eigenvalue of `V` survives in `VR` (its ≥2-dimensional eigenspace meets `w^⊥`),
  so the eigenphases of `VR` split as `a ⊎ μ` with `∑ μ ≡ ∑ a + π (mod 2π)`
  (because `det (VR) = -det V`).  `phase_budget` then gives
  `L(VR) = ∑|a| + ∑|μ| ≥ π`, sharp at `V = 1` (`CCZ`).
  `phase_budget_det` is the version with no multiplicity hypothesis:
  `L(VR) ≥ π - |Arg det V|`.

* §B  the **rank-one reflection budget**: for `R = 1 - 2ww^H` on `ℂ^d ⊗ ℂ²`,
  `trC R = 2(1 - ρ)` with `ρ = tr_C |w⟩⟨w|` a density matrix, so `σ_k = 1 - t_k`
  with `∑ t_k = 1`, and `Ψ(R) = ∑ 2 arccos (1 - t_k) ≥ π`.  Proof: `2 arccos (1-t) ≥ π t`
  (Jordan's inequality), then sum.  Sharp exactly when `ρ` is pure, i.e. `w` is a product
  vector — the `CCZ` configuration `ψ = (0,0,0,π)`.
-/

open Real Finset Matrix

namespace PhaseBudget

/-! ## §A  The odd-multiple-of-π obstruction -/

/-- An odd multiple of `π` has absolute value at least `π`. -/
theorem pi_le_abs_odd (k : ℤ) : π ≤ |π + 2 * π * k| := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hk : (1 : ℤ) ≤ |1 + 2 * k| := by
    rcases le_or_gt 0 (1 + 2 * k) with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_neg h]; omega
  have h1 : |π + 2 * π * k| = π * |((1 + 2 * k : ℤ) : ℝ)| := by
    have h2 : π + 2 * π * k = π * ((1 + 2 * k : ℤ) : ℝ) := by push_cast; ring
    rw [h2, abs_mul, abs_of_pos hπ]
  rw [h1]
  have h3 : (1:ℝ) ≤ |((1 + 2 * k : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hk
  nlinarith

/-- **Core budget lemma.**  If two lists of phases satisfy `∑ μ = ∑ a + π (mod 2π)`
then their total absolute phase is at least `π`. -/
theorem phase_budget {m n : ℕ} (a : Fin m → ℝ) (mu : Fin n → ℝ) (k : ℤ)
    (h : ∑ j, mu j = (∑ i, a i) + π + 2 * π * k) :
    π ≤ (∑ i, |a i|) + (∑ j, |mu j|) := by
  have ha : |∑ i, a i| ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
  have hm : |∑ j, mu j| ≤ ∑ j, |mu j| := Finset.abs_sum_le_sum_abs _ _
  have hsub : |(∑ j, mu j) - (∑ i, a i)| ≤ |∑ j, mu j| + |∑ i, a i| := abs_sub _ _
  have hval : (∑ j, mu j) - (∑ i, a i) = π + 2 * π * k := by rw [h]; ring
  have := pi_le_abs_odd k
  rw [hval] at hsub
  linarith

theorem pi_sub_abs_le (θ : ℝ) (k : ℤ) (h0 : -π ≤ θ) (h1 : θ ≤ π) :
    π - |θ| ≤ |θ + π + 2 * π * k| := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hneg : -|θ| ≤ θ := neg_abs_le θ
  have hpos : θ ≤ |θ| := le_abs_self θ
  rcases le_or_gt 0 k with hk | hk
  · have hkr : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    refine le_trans ?_ (le_abs_self _); nlinarith
  · have hkr : ((k:ℝ)) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    refine le_trans ?_ (neg_le_abs _); nlinarith

/-- **Determinant-deficit form.**  `L(VR) ≥ π - |Arg det V|` for a hyperplane
reflection `R`; no multiplicity hypothesis. -/
theorem phase_budget_det {n : ℕ} (b : Fin n → ℝ) (θ : ℝ) (k : ℤ)
    (h0 : -π ≤ θ) (h1 : θ ≤ π) (h : ∑ i, b i = θ + π + 2 * π * k) :
    π - |θ| ≤ ∑ i, |b i| := by
  have hb : |∑ i, b i| ≤ ∑ i, |b i| := Finset.abs_sum_le_sum_abs _ _
  rw [h] at hb
  exact le_trans (pi_sub_abs_le θ k h0 h1) hb

/-! ## §B  The rank-one reflection budget -/

/-- Jordan-chord bound `1 - 2x/π ≤ cos x` on `[0, π/2]`. -/
theorem one_sub_le_cos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π / 2) :
    1 - 2 * x / π ≤ Real.cos x := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have h := Real.mul_le_sin (x := π / 2 - x) (by linarith) (by linarith)
  rw [Real.sin_pi_div_two_sub] at h
  have he : 2 / π * (π / 2 - x) = 1 - 2 * x / π := by field_simp
  rw [he] at h; exact h

/-- `π t ≤ 2 arccos (1 - t)` for `t ∈ [0,1]`: a principal direction carrying
weight `t` of the reflected vector contributes at least `π t` to the budget. -/
theorem pi_mul_le_two_arccos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    π * t ≤ 2 * Real.arccos (1 - t) := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  set x : ℝ := π * t / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ π / 2 := by rw [hx]; nlinarith
  have hc : 1 - t ≤ Real.cos x := by
    have hcc := one_sub_le_cos hx0 hx1
    have he : 2 * x / π = t := by rw [hx]; field_simp
    rw [he] at hcc; exact hcc
  have hmono := Real.arccos_le_arccos hc
  rw [Real.arccos_cos hx0 (by linarith)] at hmono
  rw [hx] at hmono
  linarith

/-- `ψ_k = 2 arccos (1 - t_k)` lies in `[0, π]` whenever `t_k ≤ 1`. -/
theorem psi_mem {t : ℝ} (h1 : t ≤ 1) :
    0 ≤ 2 * Real.arccos (1 - t) ∧ 2 * Real.arccos (1 - t) ≤ π := by
  refine ⟨by linarith [Real.arccos_nonneg (1 - t)], ?_⟩
  have : Real.arccos (1 - t) ≤ π / 2 := by
    rw [Real.arccos]
    have := Real.arcsin_nonneg.mpr (by linarith : (0:ℝ) ≤ 1 - t)
    linarith
  linarith

/-- **BUDGET for a rank-one reflection.**  `σ_k = 1 - t_k` with `t` the spectrum of a
density matrix ⟹ `Ψ = ∑ 2 arccos σ_k ≥ π`.  Equality iff `t` is a point mass. -/
theorem budget_of_density {n : ℕ} (t : Fin n → ℝ)
    (h0 : ∀ k, 0 ≤ t k) (h1 : ∀ k, t k ≤ 1) (hs : ∑ k, t k = 1) :
    π ≤ ∑ k, 2 * Real.arccos (1 - t k) := by
  have hstep : ∀ k ∈ Finset.univ, π * t k ≤ 2 * Real.arccos (1 - t k) :=
    fun k _ => pi_mul_le_two_arccos (h0 k) (h1 k)
  have hsum := Finset.sum_le_sum hstep
  rw [← Finset.mul_sum, hs, mul_one] at hsum
  exact hsum

/-- **Reflection budget ⟹ `HSSmall`**: plugs §B straight into `AngleBudget`. -/
theorem hsSmall_of_reflection {N : Mat4} (t : Fin 4 → ℝ)
    (h0 : ∀ k, 0 ≤ t k) (h1 : ∀ k, t k ≤ 1) (hs : ∑ k, t k = 1)
    (htr : RCLike.re (Matrix.trace (Nᴴ * N))
             = ∑ k, (2 + 2 * Real.cos (2 * Real.arccos (1 - t k)))) :
    BlockU.HSSmall N :=
  AngleBudget.hsSmall_of_budget_trace (fun k => 2 * Real.arccos (1 - t k))
    (fun k => (psi_mem (h1 k)).1) (fun k => (psi_mem (h1 k)).2)
    (budget_of_density t h0 h1 hs) htr

end PhaseBudget