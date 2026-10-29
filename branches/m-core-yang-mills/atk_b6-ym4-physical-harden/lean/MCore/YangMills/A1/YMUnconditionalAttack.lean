import MCore.YangMills.A1.YMUnconditionalClosure
import MCore.YangMills.A1.B60ConcretePhysicalAdapter

/-!
Exact B6.0 attack route for the unconditional Yang--Mills closure target.

This file performs only certified transport:
B60ConcretePhysicalAdapter
  -> B6RealOpenMath
  -> YMUnconditionalClosureCertificate
  -> K14MassGap.

It does not construct a B60 inhabitant.  Therefore the scientific OPEN_MATH is
compressed to the existence of one genuine B60 adapter for a common physical
realization.
-/

namespace MCore.YangMills.A1

/-- Every genuine B6.0 adapter already contains all fields required by the
current B6RealOpenMath record. -/
def B60ConcretePhysicalAdapter.toB6RealOpenMath
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (A : B60ConcretePhysicalAdapter C F D H G O) :
    B6RealOpenMath C F D H G O where
  construction := A.constructionBlock
  infrared := A.infraredBlock
  limits := A.limitBlock
  spectralTransfer := A.transferWitness
  stateMap := A.stateMap
  observableState := A.observableState
  mappedStatesPhysical := A.mappedStatesPhysical
  observableStatesPhysical := A.observableStatesPhysical
  excitation := A.excitation
  excitationInDomain := A.excitationInDomain
  excitationPhysical := A.excitationPhysical
  excitationOrthogonalVacuum := A.excitationOrthogonalVacuum

/-- Exact single-target proposition for the B6.0 attack lane. -/
def YM_B60_UNCONDITIONAL_TARGET : Prop :=
  ∃ (C : RegulatedYM4Construction)
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G),
      Nonempty (B60ConcretePhysicalAdapter C F D H G O)

/-- A genuine B6.0 inhabitant closes the existing B6 REAL OPEN_MATH target. -/
theorem b60_unconditional_target_closes_open_math
    (h : YM_B60_UNCONDITIONAL_TARGET) :
    B6_REAL_OPEN_MATH := by
  rcases h with ⟨C, F, D, H, G, O, ⟨A⟩⟩
  exact ⟨C, F, D, H, G, O, ⟨A.toB6RealOpenMath⟩⟩

/-- The same B6.0 inhabitant constructs the exact terminal unconditional
certificate. -/
def B60ConcretePhysicalAdapter.toYMUnconditionalClosureCertificate
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (A : B60ConcretePhysicalAdapter C F D H G O) :
    YMUnconditionalClosureCertificate where
  construction := C
  frontier := F
  physicalData := D
  hamiltonian := H
  gapScale := G
  obligations := O
  witness := A.toB6RealOpenMath

/-- B6.0 existence is sufficient for the exact unconditional claim. -/
theorem b60_unconditional_target_enables_claim
    (h : YM_B60_UNCONDITIONAL_TARGET) :
    YM_UNCONDITIONAL_CLAIM := by
  rcases h with ⟨C, F, D, H, G, O, ⟨A⟩⟩
  exact ⟨A.toYMUnconditionalClosureCertificate⟩

/-- Terminal theorem-enabling route.  There are no wrappers after B6.0:
constructing one genuine adapter immediately reaches the typed mass-gap
endpoint through the already-certified chain. -/
theorem b60_unconditional_target_enables_theorem
    (h : YM_B60_UNCONDITIONAL_TARGET) :
    ∃ (D : K14PhysicalHilbertData)
      (H : K14HamiltonianOperator D)
      (G : K14GapScale D)
      (gap : D.Scale),
        K14MassGap D H G gap :=
  ym_unconditional_claim_enables_theorem
    (b60_unconditional_target_enables_claim h)

#print axioms MCore.YangMills.A1.B60ConcretePhysicalAdapter.toB6RealOpenMath
#print axioms MCore.YangMills.A1.b60_unconditional_target_closes_open_math
#print axioms MCore.YangMills.A1.b60_unconditional_target_enables_claim
#print axioms MCore.YangMills.A1.b60_unconditional_target_enables_theorem

end MCore.YangMills.A1
