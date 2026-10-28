import MCore.YangMills.A1.FinalExternal

namespace MCore.YangMills.A1.Final

/-!
Terminal signature normalization for the Yang--Mills endpoint.

This file formalizes the architectural collapse requested by the terminal
analysis: Endpoint, Gap, Habitant and Inhabitant are not four independent
obligations.  They are four names for the same final proposition.

This establishes the terminal cycle and forbids reopening the chain as if a
new mathematical target had appeared.  It does not manufacture an inhabitant:
inhabitation of any name is exactly inhabitation of FINAL_ROOT.
-/

abbrev Endpoint
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  FINAL_ROOT D H G

abbrev Gap
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  Endpoint D H G

abbrev Habitant
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  Gap D H G

abbrev Inhabitant
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  Habitant D H G

theorem endpoint_to_gap
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    Endpoint D H G → Gap D H G := id

theorem gap_to_habitant
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    Gap D H G → Habitant D H G := id

theorem habitant_to_inhabitant
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    Habitant D H G → Inhabitant D H G := id

theorem inhabitant_to_endpoint
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    Inhabitant D H G → Endpoint D H G := id

theorem terminal_cycle
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    Endpoint D H G ↔
      Gap D H G ∧ Habitant D H G ∧ Inhabitant D H G := by
  constructor
  · intro h
    exact ⟨h, h, h⟩
  · rintro ⟨h, _, _⟩
    exact h

theorem endpoint_iff_gap
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    Endpoint D H G ↔ Gap D H G := Iff.rfl

theorem endpoint_iff_habitant
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    Endpoint D H G ↔ Habitant D H G := Iff.rfl

theorem endpoint_iff_inhabitant
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    Endpoint D H G ↔ Inhabitant D H G := Iff.rfl

/-- The complete terminal signature collapses definitionally to FINAL_ROOT. -/
theorem terminal_signature_iff_FINAL_ROOT
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    (Endpoint D H G ∧ Gap D H G ∧ Habitant D H G ∧ Inhabitant D H G) ↔
      FINAL_ROOT D H G := by
  constructor
  · rintro ⟨h, _, _, _⟩
    exact h
  · intro h
    exact ⟨h, h, h, h⟩

/-- Inhabiting any terminal alias is exactly the same task as inhabiting FINAL_ROOT. -/
theorem terminal_inhabited_iff_FINAL_ROOT
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    Nonempty (Subtype fun _ : Unit => Endpoint D H G) ↔ FINAL_ROOT D H G := by
  constructor
  · rintro ⟨⟨_, h⟩⟩
    exact h
  · intro h
    exact ⟨⟨(), h⟩⟩


/-- Any terminal route hits the same final proposition; there is no fifth target. -/
theorem terminal_any_route_iff_FINAL_ROOT
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    (Endpoint D H G ∨ Gap D H G ∨ Habitant D H G ∨ Inhabitant D H G) ↔
      FINAL_ROOT D H G := by
  constructor
  · intro h
    rcases h with h | h | h | h <;> exact h
  · intro h
    exact Or.inl h

/-- The three named internal routes collapse to one terminal bit. -/
theorem three_way_collapse
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    (Gap D H G ∨ Habitant D H G ∨ Inhabitant D H G) ↔ Endpoint D H G := by
  constructor
  · intro h
    rcases h with h | h | h <;> exact h
  · intro h
    exact Or.inl h

#print axioms MCore.YangMills.A1.Final.endpoint_to_gap
#print axioms MCore.YangMills.A1.Final.terminal_cycle
#print axioms MCore.YangMills.A1.Final.terminal_signature_iff_FINAL_ROOT
#print axioms MCore.YangMills.A1.Final.terminal_inhabited_iff_FINAL_ROOT
#print axioms MCore.YangMills.A1.Final.terminal_any_route_iff_FINAL_ROOT
#print axioms MCore.YangMills.A1.Final.three_way_collapse

end MCore.YangMills.A1.Final
