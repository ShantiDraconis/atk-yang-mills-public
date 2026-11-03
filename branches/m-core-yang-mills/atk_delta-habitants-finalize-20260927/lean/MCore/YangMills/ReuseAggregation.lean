import MCore.YangMills.MinimalExternalRoute
import MCore.YangMills.A1.B60ConcretePhysicalAdapter
import MCore.PhysicalGapScaling

/-!
Local aggregation of previously certified Yang--Mills analysis into the minimal
external route.  This file does not create the missing B6 inhabitant.

Recovered provenance:
* frozen/B60-adapter-boundary-green-a6950ed
* frozen/A1-B3-B5-hardening-v2-green-c7ff632d
* frozen-SpectralCore-green-4a501490
* frozen-SpectralConcrete-green-2db15914
* frozen-SpectralMathlib-green-98f2b6a7
-/

namespace MCore.YangMills.ReuseAggregation

open MCore.YangMills.A1
open MCore.YangMills.FinalStatement
open MCore.YangMills.MinimalExternalRoute

/-- The certified B60 adapter already collapses construction, IR, limit and K30
spectral-transfer blocks to the repository's K14 mass-gap predicate. -/
theorem b60_reaches_existing_mass_gap
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (A : B60ConcretePhysicalAdapter C F D H G O) :
    ∃ gap : D.Scale, K14MassGap D H G gap :=
  b60_adapter_closes_conditional_chain A

/-- Exact remaining legacy frontier: B6, not the invalidated B3/B4/B5 wrappers. -/
theorem certified_frontier_has_one_blocker :
    (a1DecompositionV2.filter (fun b =>
      match b.status with
      | .blockingOpen _ => true
      | _ => false)).length = 1 :=
  a1_v2_has_exactly_one_blocking_node

/-- Reuse firewall: pointwise finite-cutoff positivity cannot be promoted to
uniform physical positivity. -/
theorem pointwise_gap_is_not_uniform :
    ∃ gamma : ℝ → ℝ,
      (∀ a : ℝ, 0 < a → 0 < gamma a) ∧
      ¬ ∃ m0 : ℝ, 0 < m0 ∧
        ∀ a : ℝ, 0 < a → a < 1 → m0 ≤ gamma a / a :=
  positive_cutoff_gap_not_physical_uniform

end MCore.YangMills.ReuseAggregation
