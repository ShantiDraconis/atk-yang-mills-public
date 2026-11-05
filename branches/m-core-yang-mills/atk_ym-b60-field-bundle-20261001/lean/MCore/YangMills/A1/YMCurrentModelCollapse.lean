import MCore.YangMills.A1.ExactFinalProducer

namespace MCore.YangMills.A1
namespace Final

/-- Trivial scientific frontier used only as a fidelity test. -/
def trivialFrontier : K20ScientificFrontier :=
  {
    constructiveYM4 := True
    reflectionPositiveReconstruction := True
    physicalHilbertRealization := True
    uniformExponentialClustering := True
    observableCyclicity := True
    semigroupSpectralTransfer := True
    uniformRegulatedGap := True
    continuumLimitControl := True
    thermodynamicLimitControl := True
    gapPreservedUnderLimits := True
  }

def trivialPhysicalData : K14PhysicalHilbertData :=
  {
    State := Unit
    Scale := Unit
    vacuum := ()
    zeroState := ()
    physical := fun _ => True
    orthogonalToVacuum := fun _ => True
    norm := fun _ => ()
    unitNorm := ()
    vacuum_normalized := rfl
  }

def trivialHamiltonian :
    K14HamiltonianOperator trivialPhysicalData :=
  {
    domain := fun _ => True
    act := fun _ _ => ()
    denselyDefined := True
    symmetric := True
    selfAdjoint := True
  }

def trivialGapScale :
    K14GapScale trivialPhysicalData :=
  {
    positive := fun _ => True
    gapBound := fun _ _ _ => True
  }

def trivialTransferObligations :
    K30SpectralTransferObligations
      trivialFrontier trivialPhysicalData trivialHamiltonian trivialGapScale :=
  {
    gap := ()
    positiveGap := trivial
    physicalSectorControlled := True
    observableStatesDense := True
    clusteringTransfersToSemigroup := True
    semigroupExcludesLowSpectrum := True
    exclusionFromObligations := by
      intro hF hPhys hDense hCluster hSpec psi hdom hphysical horth
      trivial
  }

def trivialTransferWitness :
    K30SpectralTransferWitness trivialTransferObligations :=
  {
    physicalSector := trivial
    density := trivial
    clusteringToSemigroup := trivial
    spectralExclusion := trivial
  }

/-- Fidelity counterexample: for every regulated construction C, the present B60
carrier is inhabited by an unrelated trivial physical model. -/
def trivialB60ForEveryConstruction
    (C : RegulatedYM4Construction) :
    B60ConcretePhysicalAdapter
      C trivialFrontier trivialPhysicalData
      trivialHamiltonian trivialGapScale trivialTransferObligations :=
  {
    stateMap := fun _ _ _ => ()
    observableState := fun _ _ _ => ()
    mappedStatesPhysical := by intro a V psi hadm; trivial
    observableStatesPhysical := by intro a V A hadm; trivial
    constructionBlock := {
      constructiveYM4 := trivial
      reflectionPositiveReconstruction := trivial
      physicalHilbertRealization := trivial
    }
    constructionFromA1 := by
      intro hm ho
      exact ⟨trivial, trivial, trivial⟩
    infraredBlock := {
      uniformExponentialClustering := trivial
      observableCyclicity := trivial
      semigroupSpectralTransfer := trivial
    }
    limitBlock := {
      uniformRegulatedGap := trivial
      continuumLimitControl := trivial
      thermodynamicLimitControl := trivial
      gapPreservedUnderLimits := trivial
    }
    excitation := ()
    excitationInDomain := trivial
    excitationPhysical := trivial
    excitationOrthogonalVacuum := trivial
    transferWitness := trivialTransferWitness
  }

theorem trivial_FINAL_ROOT_for_every_construction
    (C : RegulatedYM4Construction) :
    FINAL_ROOT trivialPhysicalData trivialHamiltonian trivialGapScale :=
  finalExternal_to_FINAL_ROOT (trivialB60ForEveryConstruction C)

#print axioms MCore.YangMills.A1.Final.trivialB60ForEveryConstruction
#print axioms MCore.YangMills.A1.Final.trivial_FINAL_ROOT_for_every_construction

end Final
end MCore.YangMills.A1
