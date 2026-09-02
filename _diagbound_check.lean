/-
`ApproxToffoli/DiagBound.lean`

Sharp bound for DIAGONAL 3-qubit unitaries of all-to-all CNOT cost ≤ 5.

Background.  Write a 3-qubit diagonal unitary as `D = diag (D 0, …, D 7)` (index
`x = 4x₁+2x₂+x₃`).  Then `Tr (CCZᴴ D) = D 0 + … + D 6 - D 7`.  Shende–Markov
(arXiv:0803.2316, Thm 30) classify diagonals by CNOT-cost through the invariants
`λ₁ = D₀₁₁D₀₀₀/(D₀₀₁D₀₁₀)`, `λ₂ = D₁₀₁D₀₀₀/(D₁₀₀D₀₀₁)`, `λ₃ = D₁₁₀D₀₀₀/(D₁₀₀D₀₁₀)`,
`ξ = D₁₁₁D₀₀₀²/(D₁₀₀D₀₁₀D₀₀₁)`: the cost is ≤ 5 iff `ξ = λ₁λ₂λ₃` or `ξ = λᵢλⱼ/λₖ`.
Setting `ρ = ξ/(λ₁λ₂λ₃)` these four conditions are `ρ ∈ {1, λ₁⁻², λ₂⁻², λ₃⁻²}`, and
clearing denominators they become the four *product* identities in
`trace_bound_of_cost_le_five` below — one for each 2-dimensional subspace `v^⊥`
of `𝔽₂³` with `wt v ≥ 2`.

The bound then follows from a purely extremal fact: if eight unit complex numbers
`t x` satisfy `∏_{x ∈ S} t x = -∏_{x ∉ S} t x` for some `S` of size 4, then
`‖∑ t x‖ ≤ 8 cos (π/8)`; equality at `t` taking the two values `e^{±iπ/8}`
four times each.  (`8 cos (π/8) = 7.3910362600…`, matching `sin (π/8)` for the
Hilbert–Schmidt distance to `CCX`.)
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

open Real Finset

namespace ApproxToffoli.DiagBound

/-! ### Numeric bounds on `cos (π/8)`, `sin (π/8)` -/

theorem c_lb : (0.9238 : ℝ) ≤ cos (π / 8) := by
  have h2 : Real.sqrt 2 ≥ 1.414 := by
    rw [show (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_le_sqrt; norm_num
  rw [Real.cos_pi_div_eight]
  have : Real.sqrt (2 + Real.sqrt 2) ≥ 1.8476 := by
    rw [show (1.8476 : ℝ) = Real.sqrt (1.8476 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_le_sqrt; nlinarith
  linarith

theorem c_ub : cos (π / 8) ≤ (0.92389 : ℝ) := by
  have h2 : Real.sqrt 2 ≤ 1.41422 := by
    rw [show (1.41422 : ℝ) = Real.sqrt (1.41422 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_le_sqrt; norm_num
  rw [Real.cos_pi_div_eight]
  have : Real.sqrt (2 + Real.sqrt 2) ≤ 1.84778 := by
    rw [show (1.84778 : ℝ) = Real.sqrt (1.84778 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_le_sqrt; nlinarith
  linarith

theorem s_lb : (0.38265 : ℝ) ≤ sin (π / 8) := by
  have h2 : Real.sqrt 2 ≤ 1.41422 := by
    rw [show (1.41422 : ℝ) = Real.sqrt (1.41422 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_le_sqrt; norm_num
  rw [Real.sin_pi_div_eight]
  have : (0.7653 : ℝ) ≤ Real.sqrt (2 - Real.sqrt 2) := by
    rw [show (0.7653 : ℝ) = Real.sqrt (0.7653 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_le_sqrt; nlinarith
  linarith

theorem s_ub : sin (π / 8) ≤ (0.38269 : ℝ) := by
  have h2 : (1.41421 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421 : ℝ) = Real.sqrt (1.41421 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_le_sqrt; norm_num
  rw [Real.sin_pi_div_eight]
  have : Real.sqrt (2 - Real.sqrt 2) ≤ 0.76538 := by
    rw [show (0.76538 : ℝ) = Real.sqrt (0.76538 ^ 2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_le_sqrt; nlinarith
  linarith

/-! ### The tangent line to `cos` at `π/8` -/

/-- Core analytic estimate: `cos (π/8) (1 - cos d) + sin (π/8) (sin d - d) ≥ 0`
for every `d ≤ 7π/8`.  Equality exactly at `d = 0`. -/
theorem key (d : ℝ) (hd : d ≤ 7 * π / 8) :
    0 ≤ cos (π / 8) * (1 - cos d) + sin (π / 8) * (sin d - d) := by
  have hpi1 : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have hpi2 : π < (3.141593 : ℝ) := Real.pi_lt_d6
  have hpipos : (0 : ℝ) < π := by linarith
  have hc := c_lb; have hc' := c_ub; have hs := s_lb; have hs' := s_ub
  by_cases h0 : d ≤ 0
  · -- `1 - cos d ≥ 0` and `sin d ≥ d` for `d ≤ 0`
    have h1 : Real.cos d ≤ 1 := Real.cos_le_one d
    have h2 : d ≤ Real.sin d := by
      have := Real.sin_le (x := -d) (by linarith)
      rw [Real.sin_neg] at this; linarith
    nlinarith
  push_neg at h0
  by_cases h1 : d ≤ 1
  · -- Taylor, via `Real.cos_bound` / `Real.sin_bound`
    have habs : |d| ≤ 1 := by rw [abs_of_pos h0]; exact h1
    have hcb := Real.cos_bound habs
    have hsb := Real.sin_bound habs
    rw [abs_of_pos h0] at hcb hsb
    have hcos : Real.cos d ≤ 1 - d ^ 2 / 2 + d ^ 4 * (5 / 96) := by
      have := abs_le.mp hcb; linarith [this.2]
    have hsin : d - d ^ 3 / 6 - d ^ 4 * (5 / 96) ≤ Real.sin d := by
      have := abs_le.mp hsb; linarith [this.1]
    nlinarith [sq_nonneg d, pow_pos h0 3, pow_pos h0 4, sq_nonneg (d - 1), h0.le]
  push_neg at h1
  by_cases h2 : d ≤ π / 2
  · -- `cos d ≤ cos 1 ≤ 5/9` and Jordan's inequality
    have hcos : Real.cos d ≤ 5 / 9 :=
      le_trans (Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) h1.le)
        Real.cos_one_le
    have hjor : 2 / π * d ≤ Real.sin d := Real.mul_le_sin (by linarith) h2
    have hjor' : 2 * d ≤ π * Real.sin d := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpipos] at hjor; linarith
    have hbd : d - Real.sin d ≤ π / 2 - 1 := by
      nlinarith [mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ π - 2)]
    nlinarith
  · -- reflect: `e = π - d ∈ [π/8, π/2]`
    push_neg at h2
    set e := π - d with he
    have he1 : π / 8 ≤ e := by simp only [he]; linarith
    have he2 : e ≤ π / 2 := by simp only [he]; linarith
    have hde : d = π - e := by simp only [he]; ring
    have hcd : Real.cos d = -Real.cos e := by rw [hde, Real.cos_pi_sub]
    have hsd : Real.sin d = Real.sin e := by rw [hde, Real.sin_pi_sub]
    have hjor : 2 / π * e ≤ Real.sin e := Real.mul_le_sin (by linarith) he2
    rw [hcd, hsd, hde]
    by_cases h3 : e ≤ π / 3
    · have hcge : (1 : ℝ) / 2 ≤ Real.cos e := by
        have := Real.cos_le_cos_of_nonneg_of_le_pi (x := e) (y := π / 3)
          (by linarith) (by linarith) h3
        rw [Real.cos_pi_div_three] at this; linarith
      have hq : 2 / π * (π / 8) ≤ 2 / π * e := mul_le_mul_of_nonneg_left he1 (by positivity)
      have h4 : 2 / π * (π / 8) = 1 / 4 := by field_simp; norm_num
      nlinarith
    · push_neg at h3
      have hcnn : (0 : ℝ) ≤ Real.cos e := Real.cos_nonneg_of_mem_Icc ⟨by linarith, he2⟩
      have hq : 2 / π * (π / 3) ≤ 2 / π * e := mul_le_mul_of_nonneg_left h3.le (by positivity)
      have h4 : 2 / π * (π / 3) = 2 / 3 := by field_simp
      nlinarith

/-- The tangent line to `cos` at `π/8` dominates `cos` on `(-∞, π]`. -/
theorem cos_le_tangent {x : ℝ} (hx : x ≤ π) :
    cos x ≤ cos (π / 8) - sin (π / 8) * (x - π / 8) := by
  have h := key (x - π / 8) (by linarith)
  have hx2 : x = (x - π / 8) + π / 8 := by ring
  rw [hx2, Real.cos_add]
  nlinarith [h]

/-! ### The eight-phase extremal lemma -/

private theorem sum_shift (φ : Fin 8 → ℝ) (a b : ℝ) :
    ∑ _i : Fin 8, (a - b * (φ _i - π / 8)) = 8 * a - b * ((∑ i, φ i) - π) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const]
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, sub_right_inj,
    mul_eq_mul_left_iff]
  left; ring

private theorem sum_cos_le_aux (φ : Fin 8 → ℝ) (hb : ∀ i, φ i ≤ π) (k : ℤ) (hk0 : 0 ≤ k)
    (hk : ∑ i, φ i = π + 2 * π * k) :
    ∑ i, Real.cos (φ i) ≤ 8 * Real.cos (π / 8) := by
  have h1 : ∑ i, Real.cos (φ i) ≤ ∑ i : Fin 8, (cos (π / 8) - sin (π / 8) * (φ i - π / 8)) :=
    Finset.sum_le_sum fun i _ => cos_le_tangent (hb i)
  rw [sum_shift φ (cos (π / 8)) (sin (π / 8)), hk] at h1
  have hs : 0 < sin (π / 8) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hkk : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hpos : 0 ≤ sin (π / 8) * (π + 2 * π * (k : ℝ) - π) := by
    have : (0 : ℝ) ≤ 2 * π * (k : ℝ) := by positivity
    nlinarith [Real.pi_pos]
  linarith

/-- **Eight-phase extremal lemma.**  If eight angles in `[-π, π]` sum to `π` modulo
`2π`, then the sum of their cosines is at most `8 cos (π/8)`.  Sharp: take four
equal to `π/8` and four equal to `-π/8`. -/
theorem sum_cos_le (φ : Fin 8 → ℝ) (hb : ∀ i, |φ i| ≤ π) (k : ℤ)
    (hk : ∑ i, φ i = π + 2 * π * k) :
    ∑ i, Real.cos (φ i) ≤ 8 * Real.cos (π / 8) := by
  rcases le_or_gt 0 k with hk0 | hk0
  · exact sum_cos_le_aux φ (fun i => (abs_le.mp (hb i)).2) k hk0 hk
  · have hsum : ∑ i, (fun i => -(φ i)) i = π + 2 * π * ((-k - 1 : ℤ) : ℝ) := by
      push_cast
      simp only [Finset.sum_neg_distrib]
      rw [hk]; ring
    have h := sum_cos_le_aux (fun i => -(φ i))
      (fun i => by have := (abs_le.mp (hb i)).1; simp; linarith) (-k - 1) (by omega) hsum
    simpa [Real.cos_neg] using h

/-! ### The complex form -/

/-- **Main extremal inequality.**  Eight unit complex numbers whose product over a
4-element set `S` is minus their product over the complement have `‖∑ t‖ ≤ 8 cos (π/8)`. -/
theorem norm_sum_le (t : Fin 8 → ℂ) (h1 : ∀ i, ‖t i‖ = 1)
    (S : Finset (Fin 8)) (hS : S.card = 4)
    (hp : ∏ i ∈ S, t i = -∏ i ∈ Sᶜ, t i) :
    ‖∑ i, t i‖ ≤ 8 * Real.cos (π / 8) := by
  classical
  have hSc : Sᶜ.card = 4 := by rw [Finset.card_compl, hS]; simp
  set w : ℂ := ∑ i, t i with hwdef
  set u : ℂ := Complex.exp (((-(Complex.arg w)) : ℝ) * Complex.I) with hudef
  have hun : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  set s : Fin 8 → ℂ := fun i => u * t i with hsdef
  have hsn : ∀ i, ‖s i‖ = 1 := by intro i; simp [hsdef, hun, h1 i]
  have hrep : ∀ i, Complex.exp (((Complex.arg (s i)) : ℝ) * Complex.I) = s i := by
    intro i
    have h := Complex.norm_mul_exp_arg_mul_I (s i)
    rw [hsn i] at h; simpa using h
  have hu2 : u * Complex.exp (((Complex.arg w) : ℝ) * Complex.I) = 1 := by
    rw [hudef, ← Complex.exp_add]
    push_cast
    rw [show (-(Complex.arg w) : ℂ) * Complex.I + (Complex.arg w : ℂ) * Complex.I = 0 by ring]
    exact Complex.exp_zero
  have hsum : ∑ i, s i = ((‖w‖ : ℝ) : ℂ) := by
    have e1 : ∑ i, s i = u * w := by simp only [hsdef, ← Finset.mul_sum, hwdef]
    rw [e1]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    rw [← mul_assoc, mul_comm u, mul_assoc, hu2, mul_one]
  have hps : ∏ i ∈ S, s i = -∏ i ∈ Sᶜ, s i := by
    have hprodS : ∏ i ∈ S, s i = u ^ 4 * ∏ i ∈ S, t i := by
      simp only [hsdef, Finset.prod_mul_distrib, Finset.prod_const, hS]
    have hprodSc : ∏ i ∈ Sᶜ, s i = u ^ 4 * ∏ i ∈ Sᶜ, t i := by
      simp only [hsdef, Finset.prod_mul_distrib, Finset.prod_const, hSc]
    rw [hprodS, hprodSc, hp]; ring
  -- now everything is phrased in terms of arguments
  set ψ : Fin 8 → ℝ := fun i => Complex.arg (s i) with hψdef
  have hψb : ∀ i, |ψ i| ≤ π := fun i => Complex.abs_arg_le_pi (s i)
  have hexp : ∀ T : Finset (Fin 8),
      Complex.exp (((∑ i ∈ T, ψ i : ℝ) : ℂ) * Complex.I) = ∏ i ∈ T, s i := by
    intro T
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ => hrep i
  have hkey : Complex.exp (((∑ i ∈ S, ψ i : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((π + ∑ i ∈ Sᶜ, ψ i : ℝ) : ℂ) * Complex.I) := by
    rw [hexp S, hps, ← hexp Sᶜ]
    rw [show (((π + ∑ i ∈ Sᶜ, ψ i : ℝ) : ℂ)) * Complex.I
        = (π : ℂ) * Complex.I + ((∑ i ∈ Sᶜ, ψ i : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hkey
  have hnr : (∑ i ∈ S, ψ i) - (∑ i ∈ Sᶜ, ψ i) = π + 2 * π * (n : ℝ) := by
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have h1' : ((∑ i ∈ S, ψ i : ℝ) : ℂ)
        = ((π + (∑ i ∈ Sᶜ, ψ i) + 2 * π * (n : ℝ) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hI
      rw [hn]; push_cast; ring
    have := Complex.ofReal_inj.mp h1'
    linarith
  set φ : Fin 8 → ℝ := fun i => if i ∈ S then ψ i else -(ψ i) with hφdef
  have hbnd : ∀ i, |φ i| ≤ π := by
    intro i
    by_cases h : i ∈ S
    · simpa [hφdef, h] using hψb i
    · simpa [hφdef, h, abs_neg] using hψb i
  have hsumφ : ∑ i, φ i = π + 2 * π * (n : ℝ) := by
    rw [← Finset.sum_add_sum_compl S φ]
    have e1 : ∑ i ∈ S, φ i = ∑ i ∈ S, ψ i :=
      Finset.sum_congr rfl fun i hi => by simp [hφdef, hi]
    have e2 : ∑ i ∈ Sᶜ, φ i = -∑ i ∈ Sᶜ, ψ i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i hi => by
        simp only [Finset.mem_compl] at hi; simp [hφdef, hi]
    rw [e1, e2]; linarith
  have hcos : ∀ i, Real.cos (φ i) = Real.cos (ψ i) := by
    intro i; by_cases h : i ∈ S <;> simp [hφdef, h, Real.cos_neg]
  have hfinal := sum_cos_le φ hbnd n hsumφ
  have hre : ‖w‖ = ∑ i, Real.cos (ψ i) := by
    have h0 := congrArg Complex.re hsum
    rw [Complex.re_sum, Complex.ofReal_re] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => by rw [← hrep i, Complex.exp_ofReal_mul_I_re]
  rw [hre]
  calc ∑ i, Real.cos (ψ i) = ∑ i, Real.cos (φ i) :=
        Finset.sum_congr rfl fun i _ => (hcos i).symm
    _ ≤ 8 * Real.cos (π / 8) := hfinal

/-! ### Application to 3-qubit diagonals -/

/-- **Diagonal bound.**  `D` is the diagonal of a 3-qubit diagonal unitary and the
hypothesis is exactly Shende–Markov's "all-to-all CNOT cost ≤ 5" (one disjunct per
2-dimensional subspace `v^⊥ ⊆ 𝔽₂³` with `wt v ≥ 2`; the first is `ξ = λ₁λ₂λ₃`, the
others are `ξ = λᵢλⱼ/λₖ`).  Then `|Tr (CCZᴴ D)| ≤ 8 cos (π/8)`. -/
theorem trace_bound_of_cost_le_five (D : Fin 8 → ℂ) (hD : ∀ x, ‖D x‖ = 1)
    (h : D 0 * D 3 * D 5 * D 6 = D 1 * D 2 * D 4 * D 7
       ∨ D 0 * D 1 * D 6 * D 7 = D 2 * D 3 * D 4 * D 5
       ∨ D 0 * D 2 * D 5 * D 7 = D 1 * D 3 * D 4 * D 6
       ∨ D 0 * D 3 * D 4 * D 7 = D 1 * D 2 * D 5 * D 6) :
    ‖D 0 + D 1 + D 2 + D 3 + D 4 + D 5 + D 6 - D 7‖ ≤ 8 * Real.cos (π / 8) := by
  classical
  set t : Fin 8 → ℂ := fun x => if x = 7 then -(D 7) else D x with htdef
  have ht1 : ∀ i, ‖t i‖ = 1 := by
    intro i; by_cases hi : i = 7 <;> simp [htdef, hi, hD]
  have htsum : ∑ i, t i = D 0 + D 1 + D 2 + D 3 + D 4 + D 5 + D 6 - D 7 := by
    simp [htdef, Fin.sum_univ_eight]
    ring
  rw [← htsum]
  rcases h with h | h | h | h
  · refine norm_sum_le t ht1 {0, 3, 5, 6} (by decide) ?_
    have e1 : (∏ i ∈ ({0, 3, 5, 6} : Finset (Fin 8)), t i) = D 0 * D 3 * D 5 * D 6 := by
      simp [htdef, Finset.prod_insert, Finset.mem_insert]; ring
    have e2 : (∏ i ∈ ({1, 2, 4, 7} : Finset (Fin 8)), t i) = -(D 1 * D 2 * D 4 * D 7) := by
      simp [htdef, Finset.prod_insert, Finset.mem_insert]; ring
    rw [show ({0, 3, 5, 6} : Finset (Fin 8))ᶜ = {1, 2, 4, 7} by decide, e1, e2]
    linear_combination h
  · refine norm_sum_le t ht1 {0, 1, 6, 7} (by decide) ?_
    have e1 : (∏ i ∈ ({0, 1, 6, 7} : Finset (Fin 8)), t i) = -(D 0 * D 1 * D 6 * D 7) := by
      simp [htdef, Finset.prod_insert, Finset.mem_insert]; ring
    have e2 : (∏ i ∈ ({2, 3, 4, 5} : Finset (Fin 8)), t i) = D 2 * D 3 * D 4 * D 5 := by
      simp [htdef, Finset.prod_insert, Finset.mem_insert]; ring
    rw [show ({0, 1, 6, 7} : Finset (Fin 8))ᶜ = {2, 3, 4, 5} by decide, e1, e2]
    linear_combination -h
  · refine norm_sum_le t ht1 {0, 2, 5, 7} (by decide) ?_
    have e1 : (∏ i ∈ ({0, 2, 5, 7} : Finset (Fin 8)), t i) = -(D 0 * D 2 * D 5 * D 7) := by
      simp [htdef, Finset.prod_insert, Finset.mem_insert]; ring
    have e2 : (∏ i ∈ ({1, 3, 4, 6} : Finset (Fin 8)), t i) = D 1 * D 3 * D 4 * D 6 := by
      simp [htdef, Finset.prod_insert, Finset.mem_insert]; ring
    rw [show ({0, 2, 5, 7} : Finset (Fin 8))ᶜ = {1, 3, 4, 6} by decide, e1, e2]
    linear_combination -h
  · refine norm_sum_le t ht1 {0, 3, 4, 7} (by decide) ?_
    have e1 : (∏ i ∈ ({0, 3, 4, 7} : Finset (Fin 8)), t i) = -(D 0 * D 3 * D 4 * D 7) := by
      simp [htdef, Finset.prod_insert, Finset.mem_insert]; ring
    have e2 : (∏ i ∈ ({1, 2, 5, 6} : Finset (Fin 8)), t i) = D 1 * D 2 * D 5 * D 6 := by
      simp [htdef, Finset.prod_insert, Finset.mem_insert]; ring
    rw [show ({0, 3, 4, 7} : Finset (Fin 8))ᶜ = {1, 2, 5, 6} by decide, e1, e2]
    linear_combination -h

end ApproxToffoli.DiagBound

#print axioms ApproxToffoli.DiagBound.trace_bound_of_cost_le_five
#print axioms ApproxToffoli.DiagBound.norm_sum_le
#print axioms ApproxToffoli.DiagBound.sum_cos_le
