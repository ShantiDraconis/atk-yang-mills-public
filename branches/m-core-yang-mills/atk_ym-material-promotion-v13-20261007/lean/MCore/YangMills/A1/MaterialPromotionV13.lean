import MCore.YangMills.A1.ExactFinalProducer
import MCore.YangMills.A1.FinalClosureCertificateV13

namespace MCore.YangMills.A1
namespace Final

/--
Single fail-closed material payload for the Yang--Mills V13 endpoint.

The payload deliberately does not contain `FINAL_ROOT`, `K14MassGap`, or a
`ProofCertificate` as input data.  It contains only the upstream scientific
ingredients required by `finalExternal_of_fields`.

Consequently, inhabiting this structure is the unique material promotion point:
all downstream closure is mechanical and kernel-checkable.
-/
structure YMMaterialPromotionPayloadV13
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    {S25 : K25ClusteringSystem}
    {U25 : K25UniformExponentialClustering S25}
    {S27 : K27RegulatedGapSystem}
    {U27 : K27UniformPositiveGap S27}
    {L27 : K27LimitControl S27}
    {W27 : K27LimitWitness S27 U27 L27} where

  /- B6 concrete A1 -> physical Hilbert coupling. -/
  stateMap :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume),
      (C.fiber a V).State → D.State

  observableState :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume),
      C.Signature.Observable → D.State

  mappedStatesPhysical :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume)
      (psi : (C.fiber a V).State),
      C.admissible a V → D.physical (stateMap a V psi)

  observableStatesPhysical :
    ∀ (a : C.Signature.Regulator) (V : C.Signature.Volume)
      (A : C.Signature.Observable),
      C.admissible a V → D.physical (observableState a V A)

  /- K23: constructive 4D continuum/reconstruction inputs. -/
  K23 : K23ConstructiveYM4Data F
  hK23 : K23ConstructionInputsHold K23

  /-
  The concrete A1 invariances must feed the same K20 model used downstream.
  This prevents promotion by an unrelated abstract model.
  -/
  constructionFromA1 :
    MeasureInvariance C →
    ObservableInvariance C →
    F.constructiveYM4 ∧
      F.reflectionPositiveReconstruction ∧
      F.physicalHilbertRealization

  /- K25: uniform exponential clustering -> infrared block. -/
  B25 : K25ClusteringToInfraredBridge F S25 U25
  hCyc : B25.observableCyclicityStillRequired
  hSemi : B25.semigroupTransferStillRequired

  /- K27: one positive regulated gap survives continuum and volume limits. -/
  B27 : K27ToFrontierBridge F S27 U27 L27 W27

  /- Non-vacuity firewall in the physical Hilbert sector. -/
  excitation : D.State
  excitationInDomain : H.domain excitation
  excitationPhysical : D.physical excitation
  excitationOrthogonalVacuum : D.orthogonalToVacuum excitation

  /-
  K30: density/physical-sector/semigroup/spectral-exclusion transfer.
  This is the final scientific transfer witness before the K29 realization.
  -/
  transferWitness : K30SpectralTransferWitness O

/--
Material payload -> exact B6 external certificate.

No endpoint theorem is assumed here; every field is consumed by the pre-existing
field-by-field constructor.
-/
def YMMaterialPromotionPayloadV13.toFinalExternal
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    {S25 : K25ClusteringSystem}
    {U25 : K25UniformExponentialClustering S25}
    {S27 : K27RegulatedGapSystem}
    {U27 : K27UniformPositiveGap S27}
    {L27 : K27LimitControl S27}
    {W27 : K27LimitWitness S27 U27 L27}
    (P : YMMaterialPromotionPayloadV13
      (C := C) (F := F) (D := D) (H := H) (G := G) (O := O)
      (S25 := S25) (U25 := U25)
      (S27 := S27) (U27 := U27) (L27 := L27) (W27 := W27)) :
    FinalExternalCertificate C F D H G O :=
  finalExternal_of_fields
    P.stateMap
    P.observableState
    P.mappedStatesPhysical
    P.observableStatesPhysical
    P.K23
    P.hK23
    P.constructionFromA1
    P.B25
    P.hCyc
    P.hSemi
    P.B27
    P.excitation
    P.excitationInDomain
    P.excitationPhysical
    P.excitationOrthogonalVacuum
    P.transferWitness

/--
The exact material promotion theorem.

Once the payload is genuinely inhabited, the already-certified external chain
produces the positive K14 mass-gap witness.  This theorem is composition only.
-/
theorem material_payload_promotes_FINAL_ROOT_V13
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    {S25 : K25ClusteringSystem}
    {U25 : K25UniformExponentialClustering S25}
    {S27 : K27RegulatedGapSystem}
    {U27 : K27UniformPositiveGap S27}
    {L27 : K27LimitControl S27}
    {W27 : K27LimitWitness S27 U27 L27}
    (P : YMMaterialPromotionPayloadV13
      (C := C) (F := F) (D := D) (H := H) (G := G) (O := O)
      (S25 := S25) (U25 := U25)
      (S27 := S27) (U27 := U27) (L27 := L27) (W27 := W27)) :
    FINAL_ROOT D H G :=
  finalExternal_to_FINAL_ROOT P.toFinalExternal

/--
Ledger form: Nonempty material payload is sufficient for terminal promotion.
The proposition remains false/unknown until an actual scientific inhabitant is
constructed; no inhabitant is manufactured in this file.
-/
theorem material_inhabitant_promotes_FINAL_ROOT_V13
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    {S25 : K25ClusteringSystem}
    {U25 : K25UniformExponentialClustering S25}
    {S27 : K27RegulatedGapSystem}
    {U27 : K27UniformPositiveGap S27}
    {L27 : K27LimitControl S27}
    {W27 : K27LimitWitness S27 U27 L27}
    (hMaterial : Nonempty (YMMaterialPromotionPayloadV13
      (C := C) (F := F) (D := D) (H := H) (G := G) (O := O)
      (S25 := S25) (U25 := U25)
      (S27 := S27) (U27 := U27) (L27 := L27) (W27 := W27))) :
    FINAL_ROOT D H G := by
  rcases hMaterial with ⟨P⟩
  exact material_payload_promotes_FINAL_ROOT_V13 P

/--
Formal promotion state used by audits.

The only positive state is tied to an actual inhabitant of the material payload;
formal-chain closure alone cannot produce it.
-/
inductive YMMaterialPromotionStateV13 where
  | notPromoted
  | promotedByMaterial
  deriving DecidableEq, Repr

def materialPromotionStateV13
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    {S25 : K25ClusteringSystem}
    {U25 : K25UniformExponentialClustering S25}
    {S27 : K27RegulatedGapSystem}
    {U27 : K27UniformPositiveGap S27}
    {L27 : K27LimitControl S27}
    {W27 : K27LimitWitness S27 U27 L27}
    (_ : Nonempty (YMMaterialPromotionPayloadV13
      (C := C) (F := F) (D := D) (H := H) (G := G) (O := O)
      (S25 := S25) (U25 := U25)
      (S27 := S27) (U27 := U27) (L27 := L27) (W27 := W27))) :
    YMMaterialPromotionStateV13 :=
  .promotedByMaterial

/--
Fail-closed theorem: adding the material-promotion interface does not itself
change the global Clay target status.
-/
theorem MATERIAL_INTERFACE_DOES_NOT_SELF_PROMOTE :
    MCore.k6_dependency.target.status = .openBridge :=
  MCore.final_core_target_still_open

#print axioms MCore.YangMills.A1.Final.YMMaterialPromotionPayloadV13.toFinalExternal
#print axioms MCore.YangMills.A1.Final.material_payload_promotes_FINAL_ROOT_V13
#print axioms MCore.YangMills.A1.Final.material_inhabitant_promotes_FINAL_ROOT_V13
#print axioms MCore.YangMills.A1.Final.MATERIAL_INTERFACE_DOES_NOT_SELF_PROMOTE

end Final
end MCore.YangMills.A1
