import MCore.K30

namespace MCore

/-- Exact terminal witness package after the K30 reduction.  It does not
construct any physical data; it packages precisely the objects whose genuine
construction remains open. -/
structure B6TerminalWitness where
  frontier : K20ScientificFrontier
  data : K14PhysicalHilbertData
  hamiltonian : K14HamiltonianOperator data
  gapScale : K14GapScale data
  blocks : K28FrontierBlocks frontier
  obligations :
    K30SpectralTransferObligations frontier data hamiltonian gapScale
  witness : K30SpectralTransferWitness obligations

/-- The B6 terminal witness is sufficient for the already-certified K30
conditional mass-gap chain. -/
theorem b6_terminal_witness_closes_mass_gap
    (W : B6TerminalWitness) :
    ∃ gap : W.data.Scale,
      K14MassGap W.data W.hamiltonian W.gapScale gap :=
  k30_witness_closes_conditional_chain W.blocks W.obligations W.witness

#print axioms MCore.b6_terminal_witness_closes_mass_gap

end MCore
