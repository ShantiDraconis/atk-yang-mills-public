import MCore.YangMills.A1.YMGapShapeF2F4F7

/-!
Canonical Yang--Mills F2 inhabitant.

This file freezes the single terminal inhabitant shape:
physical Hilbert data + Hamiltonian + vacuum data + explicit positive gap
certificate for the same physical realization.

It does not manufacture the missing Yang--Mills mathematics. The structure is
a target type. A concrete term of this type is the material object that closes
the F2 mass-gap endpoint.
-/

namespace MCore.YangMills.A1

/-- The unique terminal F2 inhabitant in the repository's existing K14 model.

The massGap field includes both strict positivity of delta and the gap bound
for all physical states orthogonal to the vacuum, through K14MassGap.
The vacuumAxiom field pins the same Hamiltonian to the distinguished vacuum.
The physicalRealization field ties the inhabitant to the same concrete B6.0
YM realization so an unrelated abstract gapped Hamiltonian cannot close YM. -/
structure YangMillsHabitant where
  start : YMClosedStart
  physicalData : K14PhysicalHilbertData
  hamiltonian : K14HamiltonianOperator physicalData
  gapScale : K14GapScale physicalData
  obligations :
    K30SpectralTransferObligations
      start.frontier physicalData hamiltonian gapScale
  physicalRealization :
    B60ConcretePhysicalAdapter
      start.regulated start.frontier physicalData
      hamiltonian gapScale obligations
  vacuumAxiom : K14VacuumAxiom physicalData hamiltonian
  delta : physicalData.Scale
  massGap : K14MassGap physicalData hamiltonian gapScale delta

/-- Exact F2 material target. No inhabitant is supplied in this file. -/
def YANG_MILLS_HABITANT_OPEN_MATH : Prop :=
  Nonempty YangMillsHabitant

/-- Projection of the explicit positive mass-gap certificate. -/
theorem YangMillsHabitant.has_mass_gap
    (Y : YangMillsHabitant) :
    ∃ delta : Y.physicalData.Scale,
      K14MassGap Y.physicalData Y.hamiltonian Y.gapScale delta :=
  ⟨Y.delta, Y.massGap⟩

/-- The same physical realization recovers the frozen F2+F4+F7 route. -/
def YangMillsHabitant.toOpenIRResidual
    (Y : YangMillsHabitant) : YMOpenIRResidual where
  start := Y.start
  physicalData := Y.physicalData
  hamiltonian := Y.hamiltonian
  gapScale := Y.gapScale
  obligations := Y.obligations
  realization := Y.physicalRealization

/-- A genuine YangMillsHabitant closes the current material open-math target. -/
theorem yang_mills_habitant_closes_open_math
    (h : YANG_MILLS_HABITANT_OPEN_MATH) :
    YM_F2_F4_F7_OPEN_MATH := by
  rcases h with ⟨Y⟩
  exact ⟨Y.toOpenIRResidual⟩

/-- Terminal theorem: the habitant itself directly exposes a positive gap. -/
theorem yang_mills_mass_gap
    (Y : YangMillsHabitant) :
    ∃ delta : Y.physicalData.Scale,
      K14MassGap Y.physicalData Y.hamiltonian Y.gapScale delta :=
  Y.has_mass_gap

/-- Full theorem-enabling route to the repository-level endpoint. -/
theorem yang_mills_habitant_enables_final
    (h : YANG_MILLS_HABITANT_OPEN_MATH) :
    ∃ (D : K14PhysicalHilbertData)
      (H : K14HamiltonianOperator D)
      (G : K14GapScale D)
      (delta : D.Scale),
        K14MassGap D H G delta :=
  yang_mills_F2_F4_F7_final
    (yang_mills_habitant_closes_open_math h)

/-- Fail-closed ledger: one material producer remains until a concrete term
of YangMillsHabitant exists. -/
def ymHabitantMaterialProducerGapCount : Nat := 1

theorem ym_habitant_material_producer_gap_count_exact :
    ymHabitantMaterialProducerGapCount = 1 := rfl

def ymHabitantStatus : String :=
  "OPEN_MATH: construct one concrete YangMillsHabitant"

#print axioms MCore.YangMills.A1.YangMillsHabitant.has_mass_gap
#print axioms MCore.YangMills.A1.yang_mills_habitant_closes_open_math
#print axioms MCore.YangMills.A1.yang_mills_mass_gap
#print axioms MCore.YangMills.A1.yang_mills_habitant_enables_final

end MCore.YangMills.A1
