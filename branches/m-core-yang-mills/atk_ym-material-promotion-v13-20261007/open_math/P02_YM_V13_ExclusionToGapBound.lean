import MCore.YangMills.A1.FiniteRegulatedSpectralV13
import MCore.YangMills.A1.SameRegulatorTransferBindingV13

namespace MCore.YangMills.A1

/-!
P02-YM V13 — superseded exclusion-only route.

The former theorem attempted to derive a statewise Hamiltonian quadratic-form
gap from `SpectralExclusionRealization`.  That signature stores
`massBelow : ℝ → ℝ` with no dependence on the state `psi`, while the desired
gap predicate is statewise.  Therefore that implication was under-specified.

The active V13 route does not use this file:
finite Hamiltonian spectral decomposition
→ same-regulator eigenvalue lower edge
→ finite quadratic-form gap
→ regulator-to-continuum limit.

This file intentionally contains no endpoint theorem, no `sorry`, no axiom,
and no replacement hypothesis that restates the mass-gap conclusion.
-/

/-- Audit marker: the exclusion-only route is not used as a terminal producer. -/
theorem exclusionOnlyRouteV13_superseded : True := by
  trivial

#print axioms MCore.YangMills.A1.exclusionOnlyRouteV13_superseded

end MCore.YangMills.A1
