import MCore.YangMills.A1.MaterialHardeningV3
import MCore.K14

namespace MCore.YangMills.A1

/--
V4 reconstruction residue.

This layer does not assume a mass gap, K30 witness, FINAL_ROOT, or any
endpoint-equivalent proposition.  It records only the compatibility needed to
send the genuine non-vacuum regulated L2 excitation carried by V3 into the
same physical K14 state space.
-/
structure PhysicalExcitationReconstructionV4
    (C : RegulatedYM4Construction)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (W : A1MaterialWitnessV3 C) where
  toPhysical :
    ∀ {a : C.Signature.Regulator} {L : C.Signature.Volume},
      RegulatedL2Vector C a L → D.State
  mapsPhysical :
    ∀ {a : C.Signature.Regulator} {L : C.Signature.Volume}
      (ψ : RegulatedL2Vector C a L),
      D.physical (toPhysical ψ)
  mapsDomain :
    ∀ {a : C.Signature.Regulator} {L : C.Signature.Volume}
      (ψ : RegulatedL2Vector C a L),
      H.domain (toPhysical ψ)
  mapsOrthogonalVacuum :
    ∀ {a : C.Signature.Regulator} {L : C.Signature.Volume}
      (ψ : RegulatedL2Vector C a L),
      regulatedInner ψ (W.positiveTransfer.vacuum a L) = 0 →
      D.orthogonalToVacuum (toPhysical ψ)
  vacuumReflectsZero :
    ∀ {a : C.Signature.Regulator} {L : C.Signature.Volume}
      (ψ : RegulatedL2Vector C a L),
      toPhysical ψ = D.vacuum →
      regulatedNormSq ψ = 0

def PhysicalExcitationReconstructionV4.excitation
    {C : RegulatedYM4Construction}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {W : A1MaterialWitnessV3 C}
    (R : PhysicalExcitationReconstructionV4 C D H W) : D.State :=
  R.toPhysical W.excitation.state

theorem PhysicalExcitationReconstructionV4.excitation_physical
    {C : RegulatedYM4Construction}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {W : A1MaterialWitnessV3 C}
    (R : PhysicalExcitationReconstructionV4 C D H W) :
    D.physical R.excitation :=
  R.mapsPhysical W.excitation.state

theorem PhysicalExcitationReconstructionV4.excitation_in_domain
    {C : RegulatedYM4Construction}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {W : A1MaterialWitnessV3 C}
    (R : PhysicalExcitationReconstructionV4 C D H W) :
    H.domain R.excitation :=
  R.mapsDomain W.excitation.state

theorem PhysicalExcitationReconstructionV4.excitation_orthogonal_vacuum
    {C : RegulatedYM4Construction}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {W : A1MaterialWitnessV3 C}
    (R : PhysicalExcitationReconstructionV4 C D H W) :
    D.orthogonalToVacuum R.excitation :=
  R.mapsOrthogonalVacuum W.excitation.state W.excitation.orthogonalVacuum

theorem PhysicalExcitationReconstructionV4.excitation_ne_vacuum
    {C : RegulatedYM4Construction}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {W : A1MaterialWitnessV3 C}
    (R : PhysicalExcitationReconstructionV4 C D H W) :
    R.excitation ≠ D.vacuum := by
  intro h
  have hz : regulatedNormSq W.excitation.state = 0 :=
    R.vacuumReflectsZero W.excitation.state h
  have hp : 0 < regulatedNormSq W.excitation.state :=
    W.excitation.positiveNorm
  rw [hz] at hp
  exact (lt_irrefl 0) hp

#print axioms MCore.YangMills.A1.PhysicalExcitationReconstructionV4.excitation_physical
#print axioms MCore.YangMills.A1.PhysicalExcitationReconstructionV4.excitation_in_domain
#print axioms MCore.YangMills.A1.PhysicalExcitationReconstructionV4.excitation_orthogonal_vacuum
#print axioms MCore.YangMills.A1.PhysicalExcitationReconstructionV4.excitation_ne_vacuum

end MCore.YangMills.A1
