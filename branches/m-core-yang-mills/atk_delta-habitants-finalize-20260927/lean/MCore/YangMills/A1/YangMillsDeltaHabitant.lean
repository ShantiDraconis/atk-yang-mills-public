import MCore.YangMills.A1.YangMillsHabitant

namespace MCore.YangMills.A1

/-!
Producer-first reduction of the frozen YangMillsHabitant.

The previous terminal structure stored `delta` and `massGap` even though the
same B6.0 physical realization already produces them through the certified
K30 -> K14 chain.  This reduced inhabitant removes that endpoint duplication.

Dependency direction:
  YMClosedStart
    -> B60ConcretePhysicalAdapter
    -> K30 spectral transfer
    -> exists delta, K14MassGap
    -> YangMillsHabitant
No edge returns to the source and no K14MassGap premise is required.
-/

structure YangMillsDeltaHabitant where
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

theorem YangMillsDeltaHabitant.produces_mass_gap
    (Y : YangMillsDeltaHabitant) :
    ∃ delta : Y.physicalData.Scale,
      K14MassGap Y.physicalData Y.hamiltonian Y.gapScale delta :=
  b60_adapter_closes_conditional_chain Y.physicalRealization

theorem YangMillsDeltaHabitant.toCanonicalHabitant
    (Y : YangMillsDeltaHabitant) :
    Nonempty YangMillsHabitant := by
  rcases Y.produces_mass_gap with ⟨delta, hgap⟩
  exact ⟨{
    start := Y.start
    physicalData := Y.physicalData
    hamiltonian := Y.hamiltonian
    gapScale := Y.gapScale
    obligations := Y.obligations
    physicalRealization := Y.physicalRealization
    vacuumAxiom := Y.vacuumAxiom
    delta := delta
    massGap := hgap
  }⟩

theorem yang_mills_delta_habitant_enables_final
    (Y : YangMillsDeltaHabitant) :
    ∃ (D : K14PhysicalHilbertData)
      (H : K14HamiltonianOperator D)
      (G : K14GapScale D)
      (delta : D.Scale),
        K14MassGap D H G delta :=
  yang_mills_habitant_enables_final Y.toCanonicalHabitant

def YANG_MILLS_DELTA_HABITANT_OPEN_MATH : Prop :=
  Nonempty YangMillsDeltaHabitant

#print axioms MCore.YangMills.A1.YangMillsDeltaHabitant.produces_mass_gap
#print axioms MCore.YangMills.A1.YangMillsDeltaHabitant.toCanonicalHabitant
#print axioms MCore.YangMills.A1.yang_mills_delta_habitant_enables_final

end MCore.YangMills.A1
