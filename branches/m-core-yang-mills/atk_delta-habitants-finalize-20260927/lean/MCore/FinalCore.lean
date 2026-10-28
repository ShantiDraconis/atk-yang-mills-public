import MCore.K30

namespace MCore

structure FinalScientificFrontier
    (F : K20ScientificFrontier)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) where
  construction : K22ConstructionBlock F
  infrared : K22InfraredBlock F
  limits : K22LimitBlock F
  spectral : K29SpectralGapRealization D H G

theorem final_frontier_blocks_close_k20
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (W : FinalScientificFrontier F D H G) :
    K20FrontierClosed F :=
  k28_blocks_recover_frontier {
    construction := W.construction
    infrared := W.infrared
    limits := W.limits
  }

theorem final_spectral_realization_implies_mass_gap
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (R : K29SpectralGapRealization D H G) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  ⟨R.gap, k29_realization_is_mass_gap R⟩

theorem final_core_closes_conditional_chain
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (W : FinalScientificFrontier F D H G) :
    K20FrontierClosed F ∧ ∃ gap : D.Scale, K14MassGap D H G gap :=
  ⟨final_frontier_blocks_close_k20 W,
   final_spectral_realization_implies_mass_gap W.spectral⟩

theorem final_core_target_still_open :
    k6_dependency.target.status = .openBridge :=
  k30_target_still_open

theorem final_core_no_promotion :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k30_no_promotion

end MCore
