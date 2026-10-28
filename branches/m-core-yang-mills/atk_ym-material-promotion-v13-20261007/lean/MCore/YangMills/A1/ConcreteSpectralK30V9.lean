import MCore.SpectralExclusion
import MCore.K30

namespace MCore.YangMills.A1

/--
Concrete spectral payload for K30.

The low-spectrum exclusion is not supplied as a field: it is derived from
`MCore.realized_exclusion` using a positive Laplace spectral measure and
exponential decay.  The remaining semantic edge is only the interpretation of
that concrete exclusion as the abstract K14/K30 `gapBound` predicate for the
same Hamiltonian.
-/
structure ConcreteSpectralK30DataV9
    (F : MCore.K20ScientificFrontier)
    (D : MCore.K14PhysicalHilbertData)
    (H : MCore.K14HamiltonianOperator D)
    (G : MCore.K14GapScale D) where
  gap : D.Scale
  positiveGap : G.positive gap

  physicalSectorControlled : Prop
  observableStatesDense : Prop
  clusteringTransfersToSemigroup : Prop

  spectral : MCore.SpectralExclusionRealization
  massNonneg :
    ∀ r : ℝ, 0 ≤ r → 0 ≤ spectral.spectral.massBelow r

  spectralExclusionToGapBound :
    (∀ r : ℝ, 0 ≤ r → r < spectral.decay.m →
      spectral.spectral.massBelow r = 0) →
    ∀ (psi : D.State) (hpsi : H.domain psi),
      D.physical psi →
      D.orthogonalToVacuum psi →
      G.gapBound gap psi (H.act psi hpsi)

/-- The spectral exclusion proposition is derived internally. -/
theorem ConcreteSpectralK30DataV9.lowSpectrumExcluded
    {F : MCore.K20ScientificFrontier}
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    (S : ConcreteSpectralK30DataV9 F D H G) :
    ∀ r : ℝ, 0 ≤ r → r < S.spectral.decay.m →
      S.spectral.spectral.massBelow r = 0 := by
  intro r hr0 hrm
  exact MCore.realized_exclusion S.spectral S.massNonneg r hr0 hrm

/-- Convert the concrete spectral payload into the existing K30 obligation
record. The K30 low-spectrum proposition is now an explicit mathematical
statement rather than an opaque bare proposition. -/
def ConcreteSpectralK30DataV9.toK30Obligations
    {F : MCore.K20ScientificFrontier}
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    (S : ConcreteSpectralK30DataV9 F D H G) :
    MCore.K30SpectralTransferObligations F D H G where
  gap := S.gap
  positiveGap := S.positiveGap
  physicalSectorControlled := S.physicalSectorControlled
  observableStatesDense := S.observableStatesDense
  clusteringTransfersToSemigroup := S.clusteringTransfersToSemigroup
  semigroupExcludesLowSpectrum :=
    ∀ r : ℝ, 0 ≤ r → r < S.spectral.decay.m →
      S.spectral.spectral.massBelow r = 0
  exclusionFromObligations := by
    intro hF hPhys hDense hCluster hSpec psi hpsi hp ho
    exact S.spectralExclusionToGapBound hSpec psi hpsi hp ho

/-- The first three K30 proof obligations remain independent of spectral
exclusion and are therefore exposed separately. -/
structure ConcreteSpectralK30WitnessV9
    {F : MCore.K20ScientificFrontier}
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    (S : ConcreteSpectralK30DataV9 F D H G) : Prop where
  physicalSector : S.physicalSectorControlled
  density : S.observableStatesDense
  clusteringToSemigroup : S.clusteringTransfersToSemigroup

/-- Build the full existing K30 witness. The fourth field is discharged by
the proved Laplace/exponential spectral exclusion theorem. -/
def ConcreteSpectralK30WitnessV9.toK30Witness
    {F : MCore.K20ScientificFrontier}
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    {S : ConcreteSpectralK30DataV9 F D H G}
    (W : ConcreteSpectralK30WitnessV9 S) :
    MCore.K30SpectralTransferWitness S.toK30Obligations where
  physicalSector := W.physicalSector
  density := W.density
  clusteringToSemigroup := W.clusteringToSemigroup
  spectralExclusion := S.lowSpectrumExcluded

/-- Direct realization obtained after the three non-spectral K30 witnesses
and the concrete spectral-to-gap semantic binding are supplied. -/
def concreteSpectralV9_builds_K29
    {F : MCore.K20ScientificFrontier}
    {D : MCore.K14PhysicalHilbertData}
    {H : MCore.K14HamiltonianOperator D}
    {G : MCore.K14GapScale D}
    (S : ConcreteSpectralK30DataV9 F D H G)
    (W : ConcreteSpectralK30WitnessV9 S)
    (hF : MCore.K20FrontierClosed F) :
    MCore.K29SpectralGapRealization D H G :=
  MCore.k30_obligations_build_realization
    S.toK30Obligations W.toK30Witness hF

#print axioms MCore.YangMills.A1.ConcreteSpectralK30DataV9.lowSpectrumExcluded
#print axioms MCore.YangMills.A1.ConcreteSpectralK30DataV9.toK30Obligations
#print axioms MCore.YangMills.A1.ConcreteSpectralK30WitnessV9.toK30Witness
#print axioms MCore.YangMills.A1.concreteSpectralV9_builds_K29

end MCore.YangMills.A1
