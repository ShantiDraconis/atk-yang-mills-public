import MCore.YangMills.A1.B60FieldBundle
import MCore.YangMills.A1.B60CanonicalPhysicalBinding
import MCore.YangMills.A1.PhysicalExcitationReconstructionV4

namespace MCore.YangMills.A1
namespace Final

/--
V5 is the exact same-model material boundary after V3/V4.

Unlike B60FieldBundle, the physical excitation fields are not free inputs:
they are derived from the non-vacuum regulated excitation in A1MaterialWitnessV3
through PhysicalExcitationReconstructionV4.

This structure still does not manufacture the genuine YM4 construction,
infrared/limit control, or K30 transfer witness. Those are the remaining
material inputs.
-/
structure CanonicalSameModelBundleV5
    (C : RegulatedYM4Construction)
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G) where
  material : A1MaterialWitnessV3 C
  reconstruction :
    PhysicalExcitationReconstructionV4 C D H material

  stateMap :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume),
      (C.fiber a V).State → D.State
  observableState :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume),
      C.Signature.Observable → D.State
  mappedStatesPhysical :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume)
      (ψ : (C.fiber a V).State),
      C.admissible a V → D.physical (stateMap a V ψ)
  observableStatesPhysical :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume)
      (A : C.Signature.Observable),
      C.admissible a V → D.physical (observableState a V A)

  K23 : K23ConstructiveYM4Data F
  hK23 : K23ConstructionInputsHold K23
  constructionFromA1 :
    MeasureInvariance C →
    ObservableInvariance C →
    F.constructiveYM4 ∧
      F.reflectionPositiveReconstruction ∧
      F.physicalHilbertRealization

  S25 : K25ClusteringSystem
  U25 : K25UniformExponentialClustering S25
  B25 : K25ClusteringToInfraredBridge F S25 U25
  hCyc : B25.observableCyclicityStillRequired
  hSemi : B25.semigroupTransferStillRequired

  S27 : K27RegulatedGapSystem
  U27 : K27UniformPositiveGap S27
  L27 : K27LimitControl S27
  W27 : K27LimitWitness S27 U27 L27
  B27 : K27ToFrontierBridge F S27 U27 L27 W27

  transferWitness : K30SpectralTransferWitness O

def CanonicalSameModelBundleV5.toFieldBundle
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (B : CanonicalSameModelBundleV5 C F D H G O) :
    B60FieldBundle C F D H G O where
  stateMap := B.stateMap
  observableState := B.observableState
  mappedStatesPhysical := B.mappedStatesPhysical
  observableStatesPhysical := B.observableStatesPhysical
  K23 := B.K23
  hK23 := B.hK23
  constructionFromA1 := B.constructionFromA1
  S25 := B.S25
  U25 := B.U25
  B25 := B.B25
  hCyc := B.hCyc
  hSemi := B.hSemi
  S27 := B.S27
  U27 := B.U27
  L27 := B.L27
  W27 := B.W27
  B27 := B.B27
  excitation := B.reconstruction.excitation
  excitationInDomain := B.reconstruction.excitation_in_domain
  excitationPhysical := B.reconstruction.excitation_physical
  excitationOrthogonalVacuum :=
    B.reconstruction.excitation_orthogonal_vacuum
  transferWitness := B.transferWitness

def CanonicalSameModelBundleV5.toCanonicalBinding
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (B : CanonicalSameModelBundleV5 C F D H G O) :
    B60CanonicalPhysicalBinding C F D H G O where
  adapter := B.toFieldBundle.toFinalExternal
  excitation_ne_vacuum := by
    change B.reconstruction.excitation ≠ D.vacuum
    exact B.reconstruction.excitation_ne_vacuum

theorem CanonicalSameModelBundleV5.closes_FINAL_ROOT
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (B : CanonicalSameModelBundleV5 C F D H G O) :
    FINAL_ROOT D H G :=
  B.toFieldBundle.closes_FINAL_ROOT

def CanonicalSameModelOpenMathV5
    (C : RegulatedYM4Construction)
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G) : Prop :=
  Nonempty (CanonicalSameModelBundleV5 C F D H G O)

theorem canonicalSameModelOpenMathV5_closes
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (h : CanonicalSameModelOpenMathV5 C F D H G O) :
    FINAL_ROOT D H G := by
  rcases h with ⟨B⟩
  exact B.closes_FINAL_ROOT

#print axioms MCore.YangMills.A1.Final.CanonicalSameModelBundleV5.toFieldBundle
#print axioms MCore.YangMills.A1.Final.CanonicalSameModelBundleV5.toCanonicalBinding
#print axioms MCore.YangMills.A1.Final.CanonicalSameModelBundleV5.closes_FINAL_ROOT
#print axioms MCore.YangMills.A1.Final.canonicalSameModelOpenMathV5_closes

end Final
end MCore.YangMills.A1
