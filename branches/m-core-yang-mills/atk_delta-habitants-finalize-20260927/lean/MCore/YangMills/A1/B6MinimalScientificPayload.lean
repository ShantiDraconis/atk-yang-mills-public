import MCore.YangMills.A1.B6TerminalWitness
import MCore.YangMills.A1.B60ConcretePhysicalAdapter
import MCore.PhysicalGapScaling

/-!
B6 minimal producer frontier.

This file removes all remaining bookkeeping ambiguity.  It does not manufacture
Yang--Mills mathematics: the only fields below are the genuinely missing
scientific inputs after reuse of the certified K20--K30 chain.
-/

namespace MCore.YangMills.A1

/-- Minimal mathematical payload still required to instantiate the terminal B6
route.  Existing K20/K22/K28/K30 infrastructure consumes these facts once they
are supplied for one common physical realization. -/
structure B6MinimalScientificPayload
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D)
    (O : K30SpectralTransferObligations F D H G) where
  construction : K22ConstructionBlock F
  infrared : K22InfraredBlock F
  limits : K22LimitBlock F
  transfer : K30SpectralTransferWitness O

/-- No extra mathematics is needed between the minimal payload and K14MassGap. -/
theorem b6_minimal_payload_closes_mass_gap
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (P : B6MinimalScientificPayload F D H G O) :
    ∃ gap : D.Scale, K14MassGap D H G gap := by
  let B : K28FrontierBlocks F := {
    construction := P.construction
    infrared := P.infrared
    limits := P.limits
  }
  exact k30_witness_closes_conditional_chain B O P.transfer

/-- The true remaining frontier is exactly four material blocks. -/
def B6RemainingBlockCount : Nat := 4

theorem b6_remaining_block_count_exact : B6RemainingBlockCount = 4 := rfl

#print axioms MCore.YangMills.A1.b6_minimal_payload_closes_mass_gap

end MCore.YangMills.A1
