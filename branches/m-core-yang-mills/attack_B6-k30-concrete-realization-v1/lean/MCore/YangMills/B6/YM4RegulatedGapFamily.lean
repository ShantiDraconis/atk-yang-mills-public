import MCore.K30
import MCore.PhysicalGapScaling

namespace MCore.YangMills.B6

/--
Concrete regulator family for the B6 frontier.

This structure records only choices already fixed by the preserved K30 /
PhysicalGapScaling interfaces:
* cutoff is a positive real physical length scale;
* volume is a natural-number regulator;
* the transfer datum at (a,L) is normalized by cutoff a;
* one positive physical mass m0 controls every sufficiently small cutoff and
  every finite volume.

No coupling parameter and no order of regulator limits are introduced here:
K30 does not determine either, so adding them would be an arbitrary
strengthening of the scientific statement.
-/
structure YM4RegulatedGapFamily where
  transfer : ℝ → ℕ → PhysicalTransferGapData
  cutoffNormalization :
    ∀ (a : ℝ) (L : ℕ), 0 < a → (transfer a L).cutoff = a
  m0 : ℝ
  a0 : ℝ
  m0_pos : 0 < m0
  a0_pos : 0 < a0
  uniformPhysicalBound :
    ∀ (a : ℝ) (L : ℕ), 0 < a → a < a0 →
      PhysicalMassLowerBound (transfer a L) m0

/-- Exact existing physical uniformity predicate recovered from a hardened B6
family.  This is a constructor/adapter, not a Yang--Mills existence proof. -/
def YM4RegulatedGapFamily.toUniformPhysicalMassLowerBound
    (R : YM4RegulatedGapFamily) :
    UniformPhysicalMassLowerBound R.transfer R.m0 R.a0 := by
  refine ⟨R.m0_pos, R.a0_pos, ?_⟩
  intro a L ha ha0
  exact ⟨R.cutoffNormalization a L ha, R.uniformPhysicalBound a L ha ha0⟩

/--
The unresolved producer is now a concrete Type-level witness rather than a
generic proposition or nominal bridge.
-/
def B6UniformLowerBound : Prop :=
  Nonempty YM4RegulatedGapFamily

/--
Fail-closed record of what K30 still does not determine.  These are not fields
of YM4RegulatedGapFamily and cannot be silently assumed by downstream code.
-/
structure K30UnderdeterminedChoices where
  couplingScopeSpecified : Bool
  regulatorLimitOrderSpecified : Bool
  deriving DecidableEq, Repr

def preservedK30Underdetermined : K30UnderdeterminedChoices :=
  { couplingScopeSpecified := false
    regulatorLimitOrderSpecified := false }

theorem k30_does_not_supply_coupling_scope :
    preservedK30Underdetermined.couplingScopeSpecified = false := rfl

theorem k30_does_not_supply_limit_order :
    preservedK30Underdetermined.regulatorLimitOrderSpecified = false := rfl

end MCore.YangMills.B6
