import MCore.YangMills.A1.B60ConcretePhysicalAdapter

namespace MCore.OpenMath.YM

open MCore.YangMills.A1

def FirstRealOpenMath
    (C : RegulatedYM4Construction)
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G) : Prop :=
  B60ConcretePhysicalOpenBridge C F D H G O

theorem close_mass_gap_from_first_real_open_math
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (h : FirstRealOpenMath C F D H G O) :
    ∃ gap : D.Scale, K14MassGap D H G gap := by
  rcases h with ⟨A⟩
  exact b60_adapter_closes_conditional_chain A

#print axioms MCore.OpenMath.YM.close_mass_gap_from_first_real_open_math

end MCore.OpenMath.YM
