/-
  ApproxToffoli.Basic
  Main theorem statement.

  **Theorem**: Any 3-qubit unitary circuit using at most 5 CX gates
  with only AB and BC connections (no direct AC) has Hilbert-Schmidt
  distance to the Toffoli gate at least sin(π/8) ≈ 0.38268.
-/

import ApproxToffoli.TraceReduction
import ApproxToffoli.TraceBound

open Matrix Complex Real

noncomputable section

/-- **Main Theorem**: For any 3-qubit unitary achievable with at most
    5 CX gates using only AB and BC connections, the Hilbert-Schmidt
    distance to the Toffoli gate is at least sin(π/8).

    Equivalently the HS fidelity is at most cos²(π/8) = (2+√2)/4. -/
theorem approxToffoli_lower_bound
    (U : Mat8) (hU : AchievableCircuit 5 U) :
    hsDistance U CCX ≥ Real.sin (Real.pi / 8) :=
  trace_bound_implies_distance U (achievable_trace_bound U hU)

end
