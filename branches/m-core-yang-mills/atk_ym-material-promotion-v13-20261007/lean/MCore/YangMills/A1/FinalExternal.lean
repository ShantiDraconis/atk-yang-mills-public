import MCore.YangMills.A1.B60ConcretePhysicalAdapter

namespace MCore.YangMills.A1
namespace Final

abbrev FinalExternalCertificate
    (C : RegulatedYM4Construction)
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G) : Type :=
  B60ConcretePhysicalAdapter C F D H G O

def FINAL_ROOT
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  ∃ gap : D.Scale, K14MassGap D H G gap

theorem finalExternal_to_FINAL_ROOT
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (E : FinalExternalCertificate C F D H G O) :
    FINAL_ROOT D H G :=
  b60_adapter_closes_conditional_chain E

end Final
end MCore.YangMills.A1
