/-
  ApproxToffoli.TraceFormula
  Compute |Tr((kron3 uA uB uC)† * CCX)|² in terms of matrix entries.
-/

import ApproxToffoli.Gates
import ApproxToffoli.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix Complex

noncomputable section

/-! ## Trace computation

We compute the trace by brute-force expansion over Fin 8 indices.
-/

set_option maxHeartbeats 6400000 in
-- Iter 755: Heartbeats raised for `trace_kron3_ccx_expanded`'s 64-leaf
-- fin_cases × fin_cases proof over Fin 8 × Fin 8 trace expansion.
/-- The trace of (kron3 uA uB uC)† * CCX in expanded form. -/
lemma trace_kron3_ccx_expanded (uA uB uC : Mat2) :
    Matrix.trace ((kron3 uA uB uC).conjTranspose * CCX) =
    star (uA 0 0 * uB 0 0 * uC 0 0) +
    star (uA 0 0 * uB 0 0 * uC 1 1) +
    star (uA 0 0 * uB 1 1 * uC 0 0) +
    star (uA 0 0 * uB 1 1 * uC 1 1) +
    star (uA 1 1 * uB 0 0 * uC 0 0) +
    star (uA 1 1 * uB 0 0 * uC 1 1) +
    star (uA 1 1 * uB 1 1 * uC 1 0) +
    star (uA 1 1 * uB 1 1 * uC 0 1) := by
  -- Expand the trace: Tr(M) = Σ_i M(i,i)
  -- M = U† * CCX, so M(i,i) = Σ_j star(U(j,i)) * CCX(j,i)
  -- For each i, only specific j give nonzero CCX(j,i)
  -- We verify by computing all 8 diagonal entries
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [Fin.sum_univ_eight]
  -- Now expand kron3 at each index pair
  simp only [kron3, Matrix.of_apply, decode3]
  -- Expand CCX at each index pair
  simp only [CCX, Matrix.of_apply, decode3, pauliX]
  -- Evaluate all Fin comparisons by deciding
  simp only [Fin.ext_iff, show (0 : Fin 2).val = 0 from rfl, show (1 : Fin 2).val = 1 from rfl]
  norm_num

/-! ## The normSq trace formula -/

/-- The squared trace norm factors into normSq of p*tC + q*offC. -/
theorem trace_normSq_formula (uA uB uC : Mat2) :
    Complex.normSq (Matrix.trace ((kron3 uA uB uC).conjTranspose * CCX)) =
    Complex.normSq (
      (uA 0 0 * (uB 0 0 + uB 1 1) + uA 1 1 * uB 0 0) * (uC 0 0 + uC 1 1) +
      uA 1 1 * uB 1 1 * (uC 0 1 + uC 1 0)
    ) := by
  rw [trace_kron3_ccx_expanded]
  -- Now LHS is normSq(star(a₀₀b₀₀c₀₀) + ... + star(a₁₁b₁₁c₀₁))
  -- = normSq(star(a₀₀b₀₀c₀₀ + ... + a₁₁b₁₁c₀₁))   by star_add
  -- = normSq(a₀₀b₀₀c₀₀ + ... + a₁₁b₁₁c₀₁)           by normSq_conj
  -- = normSq(factored expression)                        by ring
  -- First distribute star over + to get star of the whole sum
  -- Fold star(a) + star(b) + ... into star(a + b + ...)
  simp only [← star_add]
  -- star z and starRingEnd ℂ z are definitionally equal
  simp only [show ∀ z : ℂ, star z = starRingEnd ℂ z from fun _ => rfl,
             Complex.normSq_conj]
  -- Now both sides are normSq of sums of products of matrix entries.
  -- They differ only by factoring. Since normSq is a function of the value,
  -- we just need to show the arguments are equal.
  congr 1
  ring

end
