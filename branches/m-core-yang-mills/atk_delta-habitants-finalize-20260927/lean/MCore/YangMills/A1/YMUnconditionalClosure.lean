import MCore.YangMills.A1.B6RealOpenMath

/-!
Single terminal target for an unconditional Yang--Mills closure.

This module does not manufacture the missing mathematics.  It packages the
exact existing B6_REAL_OPEN_MATH existential into one certificate type and
proves that an inhabitant is sufficient to close the repository's mass-gap
endpoint.  Consequently the only remaining task for an unconditional claim is
to construct an inhabitant of `YMUnconditionalClosureCertificate`.
-/

namespace MCore.YangMills.A1

/-- One data object containing the complete material witness required by the
current fail-closed frontier.  No field is optional and no field is inferred
from source provenance or from a conditional theorem. -/
structure YMUnconditionalClosureCertificate where
  construction : RegulatedYM4Construction
  frontier : K20ScientificFrontier
  physicalData : K14PhysicalHilbertData
  hamiltonian : K14HamiltonianOperator physicalData
  gapScale : K14GapScale physicalData
  obligations :
    K30SpectralTransferObligations frontier physicalData hamiltonian gapScale
  witness :
    B6RealOpenMath
      construction frontier physicalData hamiltonian gapScale obligations

/-- Exact unconditional claim target.  This proposition is intentionally
uninhabited unless the complete scientific witness is supplied. -/
def YM_UNCONDITIONAL_CLAIM : Prop :=
  Nonempty YMUnconditionalClosureCertificate

/-- The terminal certificate is exactly the existing B6 OPEN_MATH proposition,
not a weaker wrapper. -/
theorem ym_unconditional_claim_iff_b6_real_open_math :
    YM_UNCONDITIONAL_CLAIM ↔ B6_REAL_OPEN_MATH := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.construction, C.frontier, C.physicalData, C.hamiltonian,
      C.gapScale, C.obligations, ⟨C.witness⟩⟩
  · rintro ⟨construction, frontier, physicalData, hamiltonian, gapScale,
      obligations, ⟨witness⟩⟩
    exact ⟨{
      construction := construction
      frontier := frontier
      physicalData := physicalData
      hamiltonian := hamiltonian
      gapScale := gapScale
      obligations := obligations
      witness := witness
    }⟩

/-- Exact theorem-enabling map.  Once the unconditional certificate exists,
the repository's K14 mass-gap endpoint follows with no further OPEN_MATH
transport obligation. -/
theorem ym_unconditional_certificate_enables_mass_gap
    (C : YMUnconditionalClosureCertificate) :
    ∃ gap : C.physicalData.Scale,
      K14MassGap C.physicalData C.hamiltonian C.gapScale gap :=
  b6_real_open_math_closes_mass_gap C.witness

/-- Prop-level endpoint: this is the theorem that becomes usable if and only if
the unconditional claim itself is inhabited. -/
theorem ym_unconditional_claim_enables_theorem
    (h : YM_UNCONDITIONAL_CLAIM) :
    ∃ (D : K14PhysicalHilbertData)
      (H : K14HamiltonianOperator D)
      (G : K14GapScale D)
      (gap : D.Scale),
        K14MassGap D H G gap := by
  rcases h with ⟨C⟩
  rcases ym_unconditional_certificate_enables_mass_gap C with ⟨gap, hgap⟩
  exact ⟨C.physicalData, C.hamiltonian, C.gapScale, gap, hgap⟩

#print axioms MCore.YangMills.A1.ym_unconditional_claim_iff_b6_real_open_math
#print axioms MCore.YangMills.A1.ym_unconditional_certificate_enables_mass_gap
#print axioms MCore.YangMills.A1.ym_unconditional_claim_enables_theorem

end MCore.YangMills.A1
