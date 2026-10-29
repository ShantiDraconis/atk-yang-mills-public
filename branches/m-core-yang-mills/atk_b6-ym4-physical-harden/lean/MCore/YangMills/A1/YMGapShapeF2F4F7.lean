import MCore.YangMills.A1.YMUnconditionalAttack
import MCore.YangMills.A1.B6YM4PhysicalHarden

/-!
Yang--Mills terminal gap shape: F2 + F4 + F7.

This file does not add scientific assumptions and does not manufacture a
Yang--Mills solution.  It identifies the already-existing local objects with
the closed/open/closed architecture:

C0  = regulated/classical construction already typed upstream;
O   = nonperturbative IR/physical realization;
C2  = reconstructed physical theory with a positive mass gap.

The material certificate is exactly one genuine B60 concrete physical adapter.
From that object the F7 limit block and F4 physical realization are projections,
while F2 is obtained by the already-certified K30/K14 transport chain.
-/

namespace MCore.YangMills.A1

/-- The three terminal gap shapes used by the ATK taxonomy. -/
inductive YMTerminalShape where
  | F2PositiveGap
  | F4Realization
  | F7LimitClosure
  deriving DecidableEq, Repr

/-- C0: the regulated UV/classical side is represented by the concrete
regularized construction together with its scientific frontier. -/
structure YMClosedStart where
  regulated : RegulatedYM4Construction
  frontier : K20ScientificFrontier

/-- O: the exact open material interval.  No constructor is provided here.
A value of this type is a genuine physical B6.0 realization for one common
model/Hamiltonian/sector. -/
structure YMOpenIRResidual where
  start : YMClosedStart
  physicalData : K14PhysicalHilbertData
  hamiltonian : K14HamiltonianOperator physicalData
  gapScale : K14GapScale physicalData
  obligations :
    K30SpectralTransferObligations
      start.frontier physicalData hamiltonian gapScale
  realization :
    B60ConcretePhysicalAdapter
      start.regulated start.frontier physicalData hamiltonian gapScale obligations

/-- F4: realization is literally the concrete physical adapter. -/
def YMOpenIRResidual.F4Realization
    (R : YMOpenIRResidual) :
    B60ConcretePhysicalAdapter
      R.start.regulated R.start.frontier R.physicalData
      R.hamiltonian R.gapScale R.obligations :=
  R.realization

/-- F7: cutoff/thermodynamic limit closure is an explicit material field of
the same B6.0 realization, not an inferred consequence. -/
def YMOpenIRResidual.F7LimitClosure
    (R : YMOpenIRResidual) :
    K22LimitBlock R.start.frontier :=
  R.realization.limitBlock

/-- F2: once the *same* concrete realization supplies construction, IR,
limits and spectral transfer, the already-certified transport chain produces
one strictly positive mass-gap witness in the K14 endpoint predicate. -/
theorem YMOpenIRResidual.F2PositiveGap
    (R : YMOpenIRResidual) :
    ∃ delta : R.physicalData.Scale,
      K14MassGap R.physicalData R.hamiltonian R.gapScale delta :=
  b60_adapter_closes_conditional_chain R.realization

/-- C2: the terminal reconstructed/gapped endpoint for the same physical
realization. -/
structure YMClosedEnd (R : YMOpenIRResidual) where
  delta : R.physicalData.Scale
  massGap :
    K14MassGap R.physicalData R.hamiltonian R.gapScale delta

/-- F2+F4+F7 terminal closure theorem.  The only scientific input is one
inhabitant of the exact open interval `YMOpenIRResidual`. -/
theorem yang_mills_F2_F4_F7_limit_closure
    (R : YMOpenIRResidual) :
    Nonempty (YMClosedEnd R) := by
  rcases R.F2PositiveGap with ⟨delta, hgap⟩
  exact ⟨{ delta := delta, massGap := hgap }⟩

/-- Single material producer proposition in C0 -> O -> C2 form. -/
def YM_F2_F4_F7_OPEN_MATH : Prop :=
  Nonempty YMOpenIRResidual

/-- The compressed F2+F4+F7 producer is equivalent to existence of the
previous exact B60 unconditional target.  Thus this file changes notation and
taxonomy, not scientific strength. -/
theorem ym_F2_F4_F7_open_math_iff_B60 :
    YM_F2_F4_F7_OPEN_MATH ↔ YM_B60_UNCONDITIONAL_TARGET := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.start.regulated, R.start.frontier, R.physicalData,
      R.hamiltonian, R.gapScale, R.obligations, ⟨R.realization⟩⟩
  · rintro ⟨C, F, D, H, G, O, ⟨A⟩⟩
    exact ⟨{
      start := { regulated := C, frontier := F }
      physicalData := D
      hamiltonian := H
      gapScale := G
      obligations := O
      realization := A
    }⟩

/-- Final theorem-enabling transport in the requested taxonomy. -/
theorem yang_mills_F2_F4_F7_final
    (h : YM_F2_F4_F7_OPEN_MATH) :
    ∃ (D : K14PhysicalHilbertData)
      (H : K14HamiltonianOperator D)
      (G : K14GapScale D)
      (delta : D.Scale),
        K14MassGap D H G delta :=
  b60_unconditional_target_enables_theorem
    ((ym_F2_F4_F7_open_math_iff_B60).mp h)

def ymF2F4F7Status : String :=
  "CLOSED_CONDITIONAL: F2+F4+F7 transport complete; material producer uninhabited"

def ymMaterialProducerGapCount : Nat := 1

theorem ym_material_producer_gap_count_exact :
    ymMaterialProducerGapCount = 1 := rfl

#print axioms MCore.YangMills.A1.YMOpenIRResidual.F2PositiveGap
#print axioms MCore.YangMills.A1.yang_mills_F2_F4_F7_limit_closure
#print axioms MCore.YangMills.A1.ym_F2_F4_F7_open_math_iff_B60
#print axioms MCore.YangMills.A1.yang_mills_F2_F4_F7_final

end MCore.YangMills.A1
