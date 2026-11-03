import MCore.YangMills.A1.TerminalContinuumGapV13
import MCore.YangMills.A1.SameRegulatorTransferBindingV13

noncomputable section

namespace MCore.YangMills.A1

open Filter Topology

/--
Material data still needed after the certified same-regulator finite edge.

The uniform spectral edge is not a field: it is derived from
same_regulator_eigenvalue_ge_uniformMass_V13.
-/
structure RegulatedContinuumRealizationV13
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P}
    (U : UniformRegulatorControlV2 C P B3 B4)
    (HSpace : Type)
    [NormedAddCommGroup HSpace]
    [InnerProductSpace ℂ HSpace]
    [CompleteSpace HSpace]
    [FiniteDimensional ℂ HSpace] where
  regulator : ℕ → C.Signature.Regulator
  volume : ℕ → C.Signature.Volume
  finiteHamiltonian : ℕ → FiniteRegulatedHamiltonianV13 HSpace
  sameRegulatorBinding :
    ∀ n,
      SameRegulatorHamiltonianTransferBindingV13
        B4 (finiteHamiltonian n) (regulator n) (volume n)
  admissible :
    ∀ n, C.admissible (regulator n) (volume n)
  cutoffPositive :
    ∀ n, 0 < P.cutoffValue (regulator n)
  cutoffBelow :
    ∀ n, P.cutoffValue (regulator n) < U.a0
  normSqContinuum : HSpace → ℝ
  energyContinuum : HSpace → ℝ
  normSq_tendsto :
    ∀ psi,
      Tendsto (fun _n : ℕ => ‖psi‖ ^ 2) atTop
        (𝓝 (normSqContinuum psi))
  energy_tendsto :
    ∀ psi,
      Tendsto
        (fun n =>
          Complex.re
            (inner psi ((finiteHamiltonian n).linearHamiltonian psi)))
        atTop
        (𝓝 (energyContinuum psi))

namespace RegulatedContinuumRealizationV13

variable
  {C : RegulatedYM4Construction}
  {P : A1PhysicalData C}
  {B3 : ReflectionPositivityDataV2 C P}
  {B4 : PositiveTransferDataV2 C P}
  (U : UniformRegulatorControlV2 C P B3 B4)
  {HSpace : Type}
  [NormedAddCommGroup HSpace]
  [InnerProductSpace ℂ HSpace]
  [CompleteSpace HSpace]
  [FiniteDimensional ℂ HSpace]

variable (R : RegulatedContinuumRealizationV13 U HSpace)

/-- The finite spectral edge is derived from the existing same-regulator theorem. -/
theorem derived_uniformFiniteEdge
    (n : ℕ)
    (i : Fin (Module.finrank ℂ HSpace)) :
    U.m0 ≤ (R.finiteHamiltonian n).eigenvalue i := by
  exact
    same_regulator_eigenvalue_ge_uniformMass_V13
      U
      (R.finiteHamiltonian n)
      (R.sameRegulatorBinding n)
      (R.admissible n)
      (R.cutoffPositive n)
      (R.cutoffBelow n)
      i

/-- Collapse the remaining material data into the terminal limit package. -/
def toContinuumSpectralLimit :
    ContinuumSpectralLimitV13 HSpace where
  mass := U.m0
  massPositive := U.hm0
  finiteHamiltonian := R.finiteHamiltonian
  normSqContinuum := R.normSqContinuum
  energyContinuum := R.energyContinuum
  normSq_tendsto := R.normSq_tendsto
  energy_tendsto := R.energy_tendsto
  uniformFiniteEdge := R.derived_uniformFiniteEdge U

/--
Final V13 composition from the actual same-regulator B3/B4/B5 package:
the continuum quadratic-form gap follows with mass U.m0.
-/
theorem continuum_gap
    (psi : HSpace) :
    U.m0 * R.normSqContinuum psi ≤ R.energyContinuum psi := by
  exact
    (R.toContinuumSpectralLimit U).continuum_gap_from_uniformFiniteEdge psi

theorem continuum_mass_positive :
    0 < U.m0 :=
  U.hm0

end RegulatedContinuumRealizationV13

#print axioms MCore.YangMills.A1.RegulatedContinuumRealizationV13.derived_uniformFiniteEdge
#print axioms MCore.YangMills.A1.RegulatedContinuumRealizationV13.continuum_gap

end MCore.YangMills.A1
