import MCore.YangMills.A1.RegulatedContinuumRealizationV13
import MCore.YangMills.A1.K14HamiltonianConcreteRealizationV13
import MCore.YangMills.A1.GapConcreteV13

noncomputable section

namespace MCore.YangMills.A1

/--
Recovered theorem: the continuum norm stored in RegulatedContinuumRealizationV13
is not independent material data. Since the approximating sequence is constant,
Hausdorff uniqueness of limits forces it to equal the Hilbert norm-square.
-/
theorem RegulatedContinuumRealizationV13.normSqContinuum_eq_normSq
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
    (R : RegulatedContinuumRealizationV13 U HSpace)
    (psi : HSpace) :
    R.normSqContinuum psi = ‖psi‖ ^ 2 := by
  exact
    tendsto_nhds_unique
      (R.normSq_tendsto psi)
      tendsto_const_nhds

/--
Only the actual same-model Hamiltonian identification remains between the
already-proved continuum quadratic form and the concrete K14 Hamiltonian.

This is deliberately much narrower than K23/K25/K27/K30: it says that the
continuum energy already obtained by the V13 limit construction is the energy
pairing of the concrete self-adjoint Hamiltonian used at K14.
-/
structure ContinuumHamiltonianIdentificationV15
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
    (R : RegulatedContinuumRealizationV13 U HSpace)
    (K : K14HamiltonianConcreteRealizationV13 HSpace) where
  energy_eq :
    ∀ psi : HSpace,
      R.energyContinuum psi =
        Complex.re (inner psi (K.H_op psi))

/--
Recovered direct gapBound theorem.

No low-spectrum-exclusion hypothesis appears here. The result comes directly
from the already-certified V13 continuum quadratic-form inequality.
-/
theorem RegulatedContinuumRealizationV13.recovered_gapBound_V15
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
    (R : RegulatedContinuumRealizationV13 U HSpace)
    (K : K14HamiltonianConcreteRealizationV13 HSpace)
    (I : ContinuumHamiltonianIdentificationV15 U R K)
    (psi : HSpace)
    (hpsi : K.toK14Hamiltonian.domain psi) :
    (YMGapConcreteV13 K.toRealEnergyModel).gapBound
      U.m0 psi (K.toK14Hamiltonian.act psi hpsi) := by
  rw [YMGapConcreteV13_gapBound_iff]
  rw [K.toK14_act]
  change U.m0 * ‖psi‖ ^ 2 ≤ Complex.re (inner psi (K.H_op psi))
  rw [← I.energy_eq psi]
  rw [← R.normSqContinuum_eq_normSq U psi]
  exact R.continuum_gap U psi

/--
Recovered direct K14 mass-gap theorem.

The positivity is already in UniformRegulatorControlV2; the spectral lower
bound is already in RegulatedContinuumRealizationV13.continuum_gap. Hence no
K30 spectral-exclusion bridge is needed for this concrete V13 route.
-/
theorem RegulatedContinuumRealizationV13.recovered_K14MassGap_V15
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
    (R : RegulatedContinuumRealizationV13 U HSpace)
    (K : K14HamiltonianConcreteRealizationV13 HSpace)
    (I : ContinuumHamiltonianIdentificationV15 U R K) :
    MCore.K14MassGap
      K.toRealEnergyModel.toK14
      K.toK14Hamiltonian
      (YMGapConcreteV13 K.toRealEnergyModel)
      U.m0 := by
  constructor
  · exact U.hm0
  · intro psi hpsi hphysical horthogonal
    exact R.recovered_gapBound_V15 U K I psi hpsi

/--
Existential terminal form of the recovered route.
-/
theorem RegulatedContinuumRealizationV13.recovered_FINAL_ROOT_V15
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
    (R : RegulatedContinuumRealizationV13 U HSpace)
    (K : K14HamiltonianConcreteRealizationV13 HSpace)
    (I : ContinuumHamiltonianIdentificationV15 U R K) :
    ∃ gap : K.toRealEnergyModel.toK14.Scale,
      MCore.K14MassGap
        K.toRealEnergyModel.toK14
        K.toK14Hamiltonian
        (YMGapConcreteV13 K.toRealEnergyModel)
        gap :=
  ⟨U.m0, R.recovered_K14MassGap_V15 U K I⟩

#print axioms MCore.YangMills.A1.RegulatedContinuumRealizationV13.normSqContinuum_eq_normSq
#print axioms MCore.YangMills.A1.RegulatedContinuumRealizationV13.recovered_gapBound_V15
#print axioms MCore.YangMills.A1.RegulatedContinuumRealizationV13.recovered_K14MassGap_V15
#print axioms MCore.YangMills.A1.RegulatedContinuumRealizationV13.recovered_FINAL_ROOT_V15

end MCore.YangMills.A1
