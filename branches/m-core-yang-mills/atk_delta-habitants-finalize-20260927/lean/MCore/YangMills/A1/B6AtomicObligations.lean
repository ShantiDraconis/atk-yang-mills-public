import MCore.YangMills.A1.B6RealOpenMath

/-!
Atomic decomposition of the only active Yang--Mills OPEN_MATH gate.
This file creates no scientific assumptions and no witnesses. It only exposes
the exact propositions/data already required by K22/K30 so independent work can
be reused and checked without wrapper proliferation.
-/

namespace MCore.YangMills.A1

structure B6ConstructionAtoms (F : K20ScientificFrontier) where
  constructiveYM4 : F.constructiveYM4
  reflectionPositiveReconstruction : F.reflectionPositiveReconstruction
  physicalHilbertRealization : F.physicalHilbertRealization

def B6ConstructionAtoms.toK22
    {F : K20ScientificFrontier} (A : B6ConstructionAtoms F) :
    K22ConstructionBlock F := {
  constructiveYM4 := A.constructiveYM4
  reflectionPositiveReconstruction := A.reflectionPositiveReconstruction
  physicalHilbertRealization := A.physicalHilbertRealization
}

structure B6InfraredAtoms (F : K20ScientificFrontier) where
  uniformExponentialClustering : F.uniformExponentialClustering
  observableCyclicity : F.observableCyclicity
  semigroupSpectralTransfer : F.semigroupSpectralTransfer

def B6InfraredAtoms.toK22
    {F : K20ScientificFrontier} (A : B6InfraredAtoms F) :
    K22InfraredBlock F := {
  uniformExponentialClustering := A.uniformExponentialClustering
  observableCyclicity := A.observableCyclicity
  semigroupSpectralTransfer := A.semigroupSpectralTransfer
}

structure B6LimitAtoms (F : K20ScientificFrontier) where
  uniformRegulatedGap : F.uniformRegulatedGap
  continuumLimitControl : F.continuumLimitControl
  thermodynamicLimitControl : F.thermodynamicLimitControl
  gapPreservedUnderLimits : F.gapPreservedUnderLimits

def B6LimitAtoms.toK22
    {F : K20ScientificFrontier} (A : B6LimitAtoms F) :
    K22LimitBlock F := {
  uniformRegulatedGap := A.uniformRegulatedGap
  continuumLimitControl := A.continuumLimitControl
  thermodynamicLimitControl := A.thermodynamicLimitControl
  gapPreservedUnderLimits := A.gapPreservedUnderLimits
}

structure B6TransferAtoms
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (O : K30SpectralTransferObligations F D H G) where
  physicalSector : O.physicalSectorControlled
  density : O.observableStatesDense
  clusteringToSemigroup : O.clusteringTransfersToSemigroup
  spectralExclusion : O.semigroupExcludesLowSpectrum

def B6TransferAtoms.toK30
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (A : B6TransferAtoms O) : K30SpectralTransferWitness O := {
  physicalSector := A.physicalSector
  density := A.density
  clusteringToSemigroup := A.clusteringToSemigroup
  spectralExclusion := A.spectralExclusion
}

/-- Exact atom count: 3 construction + 3 IR + 4 limit + 4 transfer. -/
def B6AtomicObligationCount : Nat := 14

theorem b6_atomic_obligation_count_exact : B6AtomicObligationCount = 14 := rfl

end MCore.YangMills.A1
