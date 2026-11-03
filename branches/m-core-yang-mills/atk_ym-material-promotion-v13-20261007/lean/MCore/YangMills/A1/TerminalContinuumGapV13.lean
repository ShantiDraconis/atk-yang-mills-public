import MCore.YangMills.A1.FiniteRegulatedSpectralV13
import Mathlib

namespace MCore.YangMills.A1

open Filter Topology

/--
Terminal V13 limit data with no low-spectrum exclusion field.
The finite spectral edge will derive exclusion constructively.
-/
structure ContinuumSpectralLimitV13
    (HSpace : Type)
    [NormedAddCommGroup HSpace]
    [InnerProductSpace ℂ HSpace]
    [CompleteSpace HSpace]
    [FiniteDimensional ℂ HSpace] where
  mass : ℝ
  massPositive : 0 < mass
  finiteHamiltonian : ℕ → FiniteRegulatedHamiltonianV13 HSpace
  normSqContinuum : HSpace → ℝ
  energyContinuum : HSpace → ℝ
  normSq_tendsto :
    ∀ psi,
      Tendsto (fun (_n : ℕ) => ‖psi‖ ^ 2) atTop
        (𝓝 (normSqContinuum psi))
  energy_tendsto :
    ∀ psi,
      Tendsto
        (fun n : ℕ =>
          Complex.re
            (inner psi ((finiteHamiltonian n).linearHamiltonian psi)))
        atTop
        (𝓝 (energyContinuum psi))
  uniformFiniteEdge :
    ∀ n i,
      mass ≤ (finiteHamiltonian n).eigenvalue i

namespace ContinuumSpectralLimitV13

variable
  {HSpace : Type}
  [NormedAddCommGroup HSpace]
  [InnerProductSpace ℂ HSpace]
  [CompleteSpace HSpace]
  [FiniteDimensional ℂ HSpace]

variable (B : ContinuumSpectralLimitV13 HSpace)

/-- Uniform finite spectral edge gives exact low-spectrum exclusion at every regulator. -/
theorem finite_lowSpectrumExclusion
    (n : ℕ)
    (psi : HSpace)
    (r : ℝ)
    (hr : r < B.mass) :
    (B.finiteHamiltonian n).massBelowFinite psi r = 0 := by
  exact
    (B.finiteHamiltonian n).massBelowFinite_eq_zero_of_weight_support_ge
      psi hr (fun i _ => B.uniformFiniteEdge n i)

/-- Therefore the eventual exclusion demanded by the continuum transfer is automatic. -/
theorem eventual_lowSpectrumExclusion
    (psi : HSpace) :
    ∀ᶠ n in atTop,
      ∀ r : ℝ, r < B.mass →
        (B.finiteHamiltonian n).massBelowFinite psi r = 0 := by
  exact Filter.Eventually.of_forall fun n r hr =>
    B.finite_lowSpectrumExclusion n psi r hr

/--
Terminal composition:
uniform finite spectral edge + norm/energy convergence imply the continuum
quadratic-form mass gap.  No continuum low-spectrum premise is assumed.
-/
theorem continuum_gap_from_uniformFiniteEdge
    (psi : HSpace) :
    B.mass * B.normSqContinuum psi ≤ B.energyContinuum psi := by
  have hfinite :
      ∀ n : ℕ,
        B.mass * ‖psi‖ ^ 2 ≤
          Complex.re
            (inner psi ((B.finiteHamiltonian n).linearHamiltonian psi)) := by
    intro n
    exact
      (B.finiteHamiltonian n).finite_mass_gap_of_weight_support_ge
        psi (fun i _ => B.uniformFiniteEdge n i)
  have hnorm :
      Tendsto
        (fun (_n : ℕ) => B.mass * ‖psi‖ ^ 2)
        atTop
        (𝓝 (B.mass * B.normSqContinuum psi)) := by
    exact tendsto_const_nhds.mul (B.normSq_tendsto psi)
  have hineq :
      ∀ᶠ n : ℕ in atTop,
        B.mass * ‖psi‖ ^ 2 ≤
          Complex.re
            (inner psi ((B.finiteHamiltonian n).linearHamiltonian psi)) :=
    Filter.Eventually.of_forall hfinite
  exact
    le_of_tendsto_of_tendsto
      hnorm
      (B.energy_tendsto psi)
      hineq

/-- Positive mass is carried explicitly by the same terminal producer. -/
theorem continuum_mass_positive : 0 < B.mass :=
  B.massPositive

end ContinuumSpectralLimitV13

#print axioms MCore.YangMills.A1.ContinuumSpectralLimitV13.finite_lowSpectrumExclusion
#print axioms MCore.YangMills.A1.ContinuumSpectralLimitV13.eventual_lowSpectrumExclusion
#print axioms MCore.YangMills.A1.ContinuumSpectralLimitV13.continuum_gap_from_uniformFiniteEdge

end MCore.YangMills.A1
