import MCore.YangMills.A1.ExactFinalProducer

namespace MCore.YangMills.A1
namespace Final

/--
Single structural field bundle for the exact B6.0 kernel closure boundary.

This packages precisely the typed inputs consumed by finalExternal_of_fields. It is not, by itself, a material Yang--Mills existence certificate.
K22 construction/infrared/limit blocks are deliberately absent because they
are already produced downstream from K23/K25/K27.
-/
structure B60FieldBundle
    (C : RegulatedYM4Construction)
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G) where
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

  excitation : D.State
  excitationInDomain : H.domain excitation
  excitationPhysical : D.physical excitation
  excitationOrthogonalVacuum : D.orthogonalToVacuum excitation

  transferWitness : K30SpectralTransferWitness O

/-- No downstream adapter gap remains after these typed fields are supplied. This is transport/assembly only. -/
def B60FieldBundle.toFinalExternal
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (B : B60FieldBundle C F D H G O) :
    FinalExternalCertificate C F D H G O :=
  finalExternal_of_fields
    B.stateMap
    B.observableState
    B.mappedStatesPhysical
    B.observableStatesPhysical
    B.K23
    B.hK23
    B.constructionFromA1
    B.B25
    B.hCyc
    B.hSemi
    B.B27
    B.excitation
    B.excitationInDomain
    B.excitationPhysical
    B.excitationOrthogonalVacuum
    B.transferWitness

/-- The single field bundle closes the already-certified Yang--Mills final root. -/
theorem B60FieldBundle.closes_FINAL_ROOT
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (B : B60FieldBundle C F D H G O) :
    FINAL_ROOT D H G :=
  FINAL_ROOT_of_fields B.toFinalExternal

/-- Exact field-level structural input after removing downstream adapters. Material closure additionally requires a canonical nondegenerate physical realization. -/
def B60FieldOpenMath
    (C : RegulatedYM4Construction)
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G) : Prop :=
  Nonempty (B60FieldBundle C F D H G O)

theorem b60FieldOpenMath_closes
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (h : B60FieldOpenMath C F D H G O) :
    FINAL_ROOT D H G := by
  rcases h with ⟨B⟩
  exact B.closes_FINAL_ROOT

#print axioms MCore.YangMills.A1.Final.B60FieldBundle.toFinalExternal
#print axioms MCore.YangMills.A1.Final.B60FieldBundle.closes_FINAL_ROOT
#print axioms MCore.YangMills.A1.Final.b60FieldOpenMath_closes

end Final
end MCore.YangMills.A1
