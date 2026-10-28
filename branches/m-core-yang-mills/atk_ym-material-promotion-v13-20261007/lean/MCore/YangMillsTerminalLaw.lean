import MCore.YangMills.A1.B60ConcretePhysicalAdapter

namespace MCore

/-! Concrete terminal certification/refutation law for the current K14 YM endpoint. -/

def YangMillsTerminalCertifies
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  ∃ gap : D.Scale, K14MassGap D H G gap

def YangMillsTerminalRefutes
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  ∀ gap : D.Scale, ¬ K14MassGap D H G gap

theorem not_yangMillsTerminalCertifies_iff_refutes
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) :
    ¬ YangMillsTerminalCertifies D H G ↔
      YangMillsTerminalRefutes D H G := by
  simp [YangMillsTerminalCertifies, YangMillsTerminalRefutes]

theorem yangMills_terminal_cert_refute_disjoint
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) :
    ¬ (YangMillsTerminalCertifies D H G ∧
       YangMillsTerminalRefutes D H G) := by
  rintro ⟨⟨gap, hgap⟩, href⟩
  exact href gap hgap

theorem b60_material_producer_certifies_terminal
    {C : YangMills.A1.RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (A : YangMills.A1.B60ConcretePhysicalAdapter C F D H G O) :
    YangMillsTerminalCertifies D H G :=
  YangMills.A1.b60_adapter_closes_conditional_chain A

theorem b60_open_bridge_certifies_terminal
    {C : YangMills.A1.RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (h : YangMills.A1.B60ConcretePhysicalOpenBridge C F D H G O) :
    YangMillsTerminalCertifies D H G :=
  YangMills.A1.b60_open_bridge_closes_conditional_chain h

end MCore
