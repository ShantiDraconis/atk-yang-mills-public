import MCore.K14
import Mathlib.Data.Real.Basic

namespace MCore.YangMills.A1

/--
V13 real-energy specialization of the K14 physical state layer.

This is not a Yang--Mills existence theorem.  It only fixes the previously
opaque K14 scale to real energies and gives an explicit meaning to the gap
predicate used by the final analytic bridge.
-/
structure RealEnergyModelV13 where
  State : Type
  vacuum : State
  zeroState : State
  physical : State → Prop
  orthogonalToVacuum : State → Prop
  normSq : State → ℝ
  energyPairing : State → State → ℝ
  unitNorm : ℝ
  vacuum_normalized : normSq vacuum = unitNorm

def RealEnergyModelV13.toK14
    (D : RealEnergyModelV13) :
    MCore.K14PhysicalHilbertData where
  State := D.State
  Scale := ℝ
  vacuum := D.vacuum
  zeroState := D.zeroState
  physical := D.physical
  orthogonalToVacuum := D.orthogonalToVacuum
  norm := D.normSq
  unitNorm := D.unitNorm
  vacuum_normalized := D.vacuum_normalized

/--
Concrete V13 gap semantics:
  m * ||psi||^2 <= <psi,H psi>_energy.
-/
def YMGapConcreteV13
    (D : RealEnergyModelV13) :
    MCore.K14GapScale D.toK14 where
  positive := fun m => 0 < (show ℝ from m)
  gapBound := fun m psi Hpsi =>
    (show ℝ from m) * D.normSq psi ≤ D.energyPairing psi Hpsi

@[simp] theorem YMGapConcreteV13_positive_iff
    (D : RealEnergyModelV13)
    (m : ℝ) :
    (YMGapConcreteV13 D).positive m ↔ 0 < m := by
  simp [YMGapConcreteV13, RealEnergyModelV13.toK14]

@[simp] theorem YMGapConcreteV13_gapBound_iff
    (D : RealEnergyModelV13)
    (m : ℝ)
    (psi Hpsi : D.State) :
    (YMGapConcreteV13 D).gapBound m psi Hpsi ↔
      m * D.normSq psi ≤ D.energyPairing psi Hpsi := by
  simp [YMGapConcreteV13, RealEnergyModelV13.toK14]

#print axioms MCore.YangMills.A1.YMGapConcreteV13_positive_iff
#print axioms MCore.YangMills.A1.YMGapConcreteV13_gapBound_iff

end MCore.YangMills.A1
