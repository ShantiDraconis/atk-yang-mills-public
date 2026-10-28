import MCore.YangMills.A1.SpectralMeasureHilbertBindingV10

noncomputable section

namespace MCore.YangMills.A1

/-- Total extension of the abstract Hamiltonian action.  On the actual domain
it agrees exactly with H.act; outside the domain we use the distinguished
zeroState only to satisfy the total-function interface. -/
def canonicalTotalHamiltonian
    (D : MCore.K14PhysicalHilbertData)
    (H : MCore.K14HamiltonianOperator D)
    (psi : D.State) : D.State := by
  classical
  exact if h : H.domain psi then H.act psi h else D.zeroState

theorem canonicalTotalHamiltonian_on_domain
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    (psi : D.State)
    (hpsi : H.domain psi) :
    canonicalTotalHamiltonian D H psi = H.act psi hpsi := by
  classical
  simp [canonicalTotalHamiltonian, hpsi]

/--
V11 removes the separate physical-surjectivity residue.

The concrete carrier is chosen to be D.State itself; toAbstract is the identity.
Hence every abstract physical, vacuum-orthogonal domain state has the concrete
preimage phi = psi.  The only remaining material input is the same-model law
turning the already-derived low-spectrum exclusion into G.gapBound.
-/
def canonicalIdentitySpectralBindingV11
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    (S : MCore.SpectralExclusionRealization)
    (rate : D.Scale)
    (ratePositive : G.positive rate)
    (spectralMassNonneg :
      ∀ r : ℝ, 0 ≤ r → 0 ≤ S.spectral.massBelow r)
    (exclusionToGapBound :
      (∀ r : ℝ, 0 ≤ r → r < S.decay.m →
        S.spectral.massBelow r = 0) →
      ∀ (psi : D.State) (hpsi : H.domain psi),
        D.physical psi →
        D.orthogonalToVacuum psi →
        G.gapBound rate psi (H.act psi hpsi)) :
    SpectralMeasureHilbertBindingV10 D H G S where
  HilbertState := D.State
  toAbstract := id
  physical := D.physical
  vacuumOrthogonal := D.orthogonalToVacuum
  inDomain := H.domain
  hamiltonian := canonicalTotalHamiltonian D H
  rate := rate
  ratePositive := ratePositive
  mapsPhysical := by
    intro psi hp
    exact hp
  mapsOrthogonal := by
    intro psi ho
    exact ho
  mapsDomain := by
    intro psi hd
    exact hd
  intertwines := by
    intro psi hd
    simpa using canonicalTotalHamiltonian_on_domain psi hd
  spectralMassNonneg := spectralMassNonneg
  exclusionToGapBound := by
    intro hspec psi hp ho hd
    simpa [canonicalTotalHamiltonian_on_domain psi hd] using
      exclusionToGapBound hspec psi hd hp ho

/-- For the canonical identity binding, physical-sector coverage is a theorem:
the required preimage is the state itself. -/
theorem canonicalIdentitySpectralBindingV11_massGap
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    (S : MCore.SpectralExclusionRealization)
    (rate : D.Scale)
    (ratePositive : G.positive rate)
    (spectralMassNonneg :
      ∀ r : ℝ, 0 ≤ r → 0 ≤ S.spectral.massBelow r)
    (exclusionToGapBound :
      (∀ r : ℝ, 0 ≤ r → r < S.decay.m →
        S.spectral.massBelow r = 0) →
      ∀ (psi : D.State) (hpsi : H.domain psi),
        D.physical psi →
        D.orthogonalToVacuum psi →
        G.gapBound rate psi (H.act psi hpsi)) :
    MCore.K14MassGap D H G rate := by
  let B :=
    canonicalIdentitySpectralBindingV11
      S rate ratePositive spectralMassNonneg exclusionToGapBound
  apply spectralMeasureV10_massGap B
  intro psi hp ho hd
  exact ⟨psi, rfl, hp, ho, hd⟩

#print axioms MCore.YangMills.A1.canonicalTotalHamiltonian_on_domain
#print axioms MCore.YangMills.A1.canonicalIdentitySpectralBindingV11
#print axioms MCore.YangMills.A1.canonicalIdentitySpectralBindingV11_massGap

end MCore.YangMills.A1
