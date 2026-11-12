/-
The two formalized circuits for the conditional, side by side.

* `Line.exactLine_66_T`: on a line, at most `66 (N-1)` CNOTs, `36 (N-1)` T gates and
  `4N - 1` rotations.
* `Qulin.qulin_goal`: the Huang–Palsberg circuit (any two qubits may interact) has
  exactly `qulinCnots N` CNOTs, and its one-qubit gates are `qulinT N` T gates and
  `qulinR N` rotations.

This file records the comparison of these numbers, and that a circuit on a line is in
particular a circuit with no layout constraint.
-/
import Mathlib
import ApproxToffoli.Line.TMain
import ApproxToffoli.Free.QulinMain

namespace Qulin

open Free

/-- The line circuit has fewer CNOTs than the Huang–Palsberg circuit, for every `N ≥ 6`. -/
theorem line_cnots_lt (N : ℕ) (hN : 6 ≤ N) : 66 * (N - 1) < qulinCnots N := by
  unfold qulinCnots
  split_ifs <;> omega

/-- The line circuit has fewer T gates than the Huang–Palsberg circuit, for every `N ≥ 6`. -/
theorem line_T_lt (N : ℕ) (hN : 6 ≤ N) : 36 * (N - 1) < qulinT N := by
  unfold qulinT
  split_ifs <;> omega

/-- The line circuit has fewer rotations than the Huang–Palsberg circuit, for every
`N ≥ 8`. -/
theorem line_R_lt (N : ℕ) (hN : 8 ≤ N) : 4 * N - 1 < qulinR N := by
  unfold qulinR
  split_ifs <;> omega

/-- The exact line circuit, read as a circuit with no layout constraint: the same
conditional (target qubit `0`), with fewer CNOTs and fewer T gates than the
Huang–Palsberg circuit on the same number of qubits. -/
theorem line_circuit_beats_qulin (N : ℕ) (hN : 6 ≤ N) :
    ∃ c : List (Gate N),
      UnitaryGates c ∧ circMat c = Line.condMat (⟨0, by omega⟩ : Fin N) ∧
      cnots c < cnots (qulin N (by omega)) ∧
      ∃ t r : ℕ, TR c t r ∧ t < qulinT N ∧ r ≤ 4 * N - 1 := by
  obtain ⟨c, hu, hc, hm, t, r, htr, ht, hr⟩ := Line.exactLine_66_T N (by omega)
  refine ⟨ofLine c, unitaryGates_ofLine hu, ?_, ?_, t, r, tr_ofLine htr, ?_, hr⟩
  · rw [circMat_ofLine, hm]
  · rw [cnots_ofLine, cnots_qulin N hN]
    exact lt_of_le_of_lt hc (line_cnots_lt N hN)
  · exact lt_of_le_of_lt ht (line_T_lt N hN)

end Qulin
