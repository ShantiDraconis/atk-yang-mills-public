import MCore.K0

namespace MCore.YM

/-- Kernel-portable semantic interface for the Yang--Mills existence and
    positive mass-gap endpoint. -/
structure EndpointSemantics where
  ExistsQuantumTheory : Prop
  GapWitness : Type
  Positive : GapWitness → Prop
  HasMassGap : GapWitness → Prop

/-- Existence of the quantum theory together with a positive gap witness.
    This only states the endpoint. -/
def FinalEndpoint (S : EndpointSemantics) : Prop :=
  S.ExistsQuantumTheory ∧
    ∃ Δ : S.GapWitness, S.Positive Δ ∧ S.HasMassGap Δ

/-- Adapter obligation connecting the abstract endpoint to a concrete
    construction/spectral semantics. -/
structure ConcreteTheoryAdapter (S : EndpointSemantics) where
  ConcreteExists : Prop
  ConcretePositive : S.GapWitness → Prop
  ConcreteHasMassGap : S.GapWitness → Prop
  existence_match : S.ExistsQuantumTheory ↔ ConcreteExists
  positive_match : ∀ Δ, S.Positive Δ ↔ ConcretePositive Δ
  gap_match : ∀ Δ, S.HasMassGap Δ ↔ ConcreteHasMassGap Δ

theorem endpoint_transport
    (S : EndpointSemantics)
    (A : ConcreteTheoryAdapter S)
    (h : FinalEndpoint S) :
    A.ConcreteExists ∧
      ∃ Δ : S.GapWitness,
        A.ConcretePositive Δ ∧ A.ConcreteHasMassGap Δ := by
  rcases h with ⟨hex, Δ, hpos, hgap⟩
  exact ⟨A.existence_match.mp hex, Δ,
    (A.positive_match Δ).mp hpos,
    (A.gap_match Δ).mp hgap⟩

#print axioms endpoint_transport

end MCore.YM
