import MCore.YangMills.A1.TerminalSignatureCycleV13

namespace MCore.YangMills.A1.Final

/--
Audit-state polarity for the terminal frontier. This is bookkeeping for whether
the unique endpoint is still classified as open or has been certified closed.
It is deliberately separate from the mathematical proposition FINAL_ROOT.
-/
inductive FrontierState where
  | openMath
  | closedMath
deriving DecidableEq, Repr

def FrontierState.flip : FrontierState → FrontierState
  | .openMath => .closedMath
  | .closedMath => .openMath

theorem flip_open :
    FrontierState.flip .openMath = .closedMath := rfl

theorem flip_closed :
    FrontierState.flip .closedMath = .openMath := rfl

theorem flip_involutive (s : FrontierState) :
    FrontierState.flip (FrontierState.flip s) = s := by
  cases s <;> rfl

theorem flip_ne_self (s : FrontierState) :
    FrontierState.flip s ≠ s := by
  cases s <;> decide

/--
The status transition has two opposite labels, while the mathematical target
under either label remains the same unique endpoint FINAL_ROOT.
-/
def FrontierTarget
    (_ : FrontierState)
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  FINAL_ROOT D H G

theorem frontier_target_status_invariant
    (s : FrontierState)
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    FrontierTarget (FrontierState.flip s) D H G ↔
      FrontierTarget s D H G := Iff.rfl

theorem open_target_iff_closed_target
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    FrontierTarget .openMath D H G ↔
      FrontierTarget .closedMath D H G := Iff.rfl

#print axioms MCore.YangMills.A1.Final.flip_involutive
#print axioms MCore.YangMills.A1.Final.flip_ne_self
#print axioms MCore.YangMills.A1.Final.frontier_target_status_invariant
#print axioms MCore.YangMills.A1.Final.open_target_iff_closed_target

end MCore.YangMills.A1.Final
