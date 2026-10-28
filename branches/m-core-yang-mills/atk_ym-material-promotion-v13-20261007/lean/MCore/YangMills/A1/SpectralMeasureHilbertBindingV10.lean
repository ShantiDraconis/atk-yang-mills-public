import MCore.YangMills.A1.ConcreteSpectralK30V9
import MCore.SpectralConcreteAdapter

namespace MCore.YangMills.A1

/--
V10 binds a concrete Hilbert realization to the spectral-measure exclusion
proved in V9.

The low-spectrum exclusion itself is not assumed.  It is derived by
`ConcreteSpectralK30DataV9.lowSpectrumExcluded`.  The only semantic residue
is the model-specific statement that vanishing spectral mass below the decay
rate implies the abstract `G.gapBound` relation for the same Hamiltonian.
-/
structure SpectralMeasureHilbertBindingV10
    (D : MCore.K14PhysicalHilbertData)
    (H : MCore.K14HamiltonianOperator D)
    (G : MCore.K14GapScale D)
    (S : MCore.SpectralExclusionRealization) where
  HilbertState : Type
  toAbstract : HilbertState → D.State
  physical : HilbertState → Prop
  vacuumOrthogonal : HilbertState → Prop
  inDomain : HilbertState → Prop
  hamiltonian : HilbertState → HilbertState

  rate : D.Scale
  ratePositive : G.positive rate

  mapsPhysical :
    ∀ psi, physical psi → D.physical (toAbstract psi)
  mapsOrthogonal :
    ∀ psi, vacuumOrthogonal psi →
      D.orthogonalToVacuum (toAbstract psi)
  mapsDomain :
    ∀ psi, inDomain psi → H.domain (toAbstract psi)
  intertwines :
    ∀ (psi) (hd : inDomain psi),
      toAbstract (hamiltonian psi) =
        H.act (toAbstract psi) (mapsDomain psi hd)

  spectralMassNonneg :
    ∀ r : ℝ, 0 ≤ r → 0 ≤ S.spectral.massBelow r

  exclusionToGapBound :
    (∀ r : ℝ, 0 ≤ r → r < S.decay.m →
      S.spectral.massBelow r = 0) →
    ∀ psi,
      physical psi →
      vacuumOrthogonal psi →
      inDomain psi →
      G.gapBound rate
        (toAbstract psi)
        (toAbstract (hamiltonian psi))

/-- V9's analytic theorem discharges the low-spectrum exclusion used by V10. -/
theorem SpectralMeasureHilbertBindingV10.lowSpectrumExcluded
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    {S : MCore.SpectralExclusionRealization}
    (B : SpectralMeasureHilbertBindingV10 D H G S) :
    ∀ r : ℝ, 0 ≤ r → r < S.decay.m →
      S.spectral.massBelow r = 0 := by
  intro r hr0 hrm
  exact MCore.realized_exclusion S B.spectralMassNonneg r hr0 hrm

/-- Construct the existing concrete Hilbert adapter with its spectral lower
bound derived from the V9 exclusion theorem. -/
def SpectralMeasureHilbertBindingV10.toConcreteHilbertAdapter
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    {S : MCore.SpectralExclusionRealization}
    (B : SpectralMeasureHilbertBindingV10 D H G S) :
    MCore.ConcreteHilbertAdapter D H G where
  HilbertState := B.HilbertState
  toAbstract := B.toAbstract
  physical := B.physical
  vacuumOrthogonal := B.vacuumOrthogonal
  inDomain := B.inDomain
  hamiltonian := B.hamiltonian
  rate := B.rate
  ratePositive := B.ratePositive
  mapsPhysical := B.mapsPhysical
  mapsOrthogonal := B.mapsOrthogonal
  mapsDomain := B.mapsDomain
  intertwines := B.intertwines
  spectralLowerBound := by
    intro psi hp ho hd
    exact B.exclusionToGapBound
      B.lowSpectrumExcluded psi hp ho hd

/-- With physical-sector coverage, the same-model V10 binding closes the
existing K14 mass-gap predicate mechanically. -/
theorem spectralMeasureV10_massGap
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    {S : MCore.SpectralExclusionRealization}
    (B : SpectralMeasureHilbertBindingV10 D H G S)
    (surjectivePhysical :
      ∀ psi : D.State,
        D.physical psi →
        D.orthogonalToVacuum psi →
        H.domain psi →
        ∃ phi : B.HilbertState,
          B.toAbstract phi = psi ∧
          B.physical phi ∧
          B.vacuumOrthogonal phi ∧
          B.inDomain phi) :
    MCore.K14MassGap D H G B.rate := by
  exact MCore.concrete_adapter_mass_gap
    B.toConcreteHilbertAdapter surjectivePhysical

#print axioms MCore.YangMills.A1.SpectralMeasureHilbertBindingV10.lowSpectrumExcluded
#print axioms MCore.YangMills.A1.SpectralMeasureHilbertBindingV10.toConcreteHilbertAdapter
#print axioms MCore.YangMills.A1.spectralMeasureV10_massGap

end MCore.YangMills.A1
