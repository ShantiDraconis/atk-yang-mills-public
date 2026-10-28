import MCore.YangMills.A1.B6HardenedLimitCore
import MCore.PhysicalGapScaling

/-!
Concrete physical hardening for YM/B6.

This file fixes the semantic choices left implicit by B6RegulatedGapFamily:
* four-dimensional SU(N), N >= 2;
* one fixed renormalized coupling at a physical reference scale;
* cutoff-dependent bare coupling is allowed and explicit;
* the gap scale is a physical mass, while the one-step lattice gap is dimensionless;
* the order/path of cutoff removal and infinite-volume limits is explicit data.

No Yang--Mills mass-gap witness is constructed here.
-/

namespace MCore.YangMills.A1

inductive YM4BoundaryCondition where
  | periodic
  deriving DecidableEq, Repr

inductive YM4LimitOrder where
  | thermodynamicThenContinuum
  | continuumThenThermodynamic
  | jointPhysicalPath
  deriving DecidableEq, Repr

structure YM4PhysicalRegime where
  gaugeRank : ℕ
  gaugeRank_ge_two : 2 ≤ gaugeRank
  spacetimeDimension : ℕ
  dimension_is_four : spacetimeDimension = 4
  referenceScale : ℝ
  referenceScale_pos : 0 < referenceScale
  renormalizedCoupling : ℝ
  renormalizedCoupling_pos : 0 < renormalizedCoupling
  boundaryCondition : YM4BoundaryCondition
  limitOrder : YM4LimitOrder

def YM4PhysicalCutoff (a0 : ℝ) : Type :=
  {a : ℝ // 0 < a ∧ a < a0}

def YM4PhysicalVolume : Type :=
  {L : ℕ // 0 < L}

structure YM4RegulatedGapFamily where
  regime : YM4PhysicalRegime
  cutoffWindow : ℝ
  cutoffWindow_pos : 0 < cutoffWindow

  bareCoupling : YM4PhysicalCutoff cutoffWindow → ℝ
  bareCoupling_pos : ∀ a, 0 < bareCoupling a

  wilsonBeta : YM4PhysicalCutoff cutoffWindow → ℝ
  wilsonBeta_relation :
    ∀ a,
      wilsonBeta a =
        (2 * (regime.gaugeRank : ℝ)) / ((bareCoupling a) ^ 2)

  latticeGap :
    YM4PhysicalCutoff cutoffWindow → YM4PhysicalVolume → ℝ
  latticeGap_nonneg : ∀ a L, 0 ≤ latticeGap a L

  physicalGap :
    YM4PhysicalCutoff cutoffWindow → YM4PhysicalVolume → ℝ
  physicalGap_nonneg : ∀ a L, 0 ≤ physicalGap a L

  physical_gap_scaling :
    ∀ a L, physicalGap a L = latticeGap a L / (a.1)

def YM4RegulatedGapFamily.toB6
    (R : YM4RegulatedGapFamily) : B6RegulatedGapFamily where
  Cutoff := YM4PhysicalCutoff R.cutoffWindow
  Volume := YM4PhysicalVolume
  Scale := ℝ
  gap := R.physicalGap
  positive := fun m => 0 < m
  lowerBound := fun m gap => m ≤ gap

structure YM4UniformPhysicalLowerBound (R : YM4RegulatedGapFamily) where
  mass : ℝ
  mass_pos : 0 < mass
  uniform : ∀ a L, mass ≤ R.physicalGap a L

def YM4UniformPhysicalLowerBound.toB6
    {R : YM4RegulatedGapFamily}
    (U : YM4UniformPhysicalLowerBound R) :
    B6UniformLowerBound R.toB6 where
  delta := U.mass
  deltaPositive := U.mass_pos
  uniform := U.uniform

structure YM4IRSystem (R : YM4RegulatedGapFamily) where
  Observable : Type
  observableNorm : Observable → ℝ
  observableNorm_nonneg : ∀ O, 0 ≤ observableNorm O
  connectedCorrelation :
    YM4PhysicalCutoff R.cutoffWindow →
    YM4PhysicalVolume →
    Observable → Observable → ℝ → ℝ

structure YM4IRUniformWeak
    {R : YM4RegulatedGapFamily}
    (S : YM4IRSystem R) where
  prefactorAt :
    YM4PhysicalCutoff R.cutoffWindow → YM4PhysicalVolume → ℝ
  massAt :
    YM4PhysicalCutoff R.cutoffWindow → YM4PhysicalVolume → ℝ
  prefactor_nonneg : ∀ a L, 0 ≤ prefactorAt a L
  mass_pos : ∀ a L, 0 < massAt a L
  decay :
    ∀ a L A B r, 0 ≤ r →
      |S.connectedCorrelation a L A B r| ≤
        (prefactorAt a L) * S.observableNorm A * S.observableNorm B *
          Real.exp (-(massAt a L) * r)

structure YM4IRUniformStrong
    {R : YM4RegulatedGapFamily}
    (S : YM4IRSystem R) where
  prefactor : ℝ
  mass : ℝ
  prefactor_nonneg : 0 ≤ prefactor
  mass_pos : 0 < mass
  decay :
    ∀ a L A B r, 0 ≤ r →
      |S.connectedCorrelation a L A B r| ≤
        prefactor * S.observableNorm A * S.observableNorm B *
          Real.exp (-mass * r)

def YM4D_uniform_IR_mass_gap_producer
    (R : YM4RegulatedGapFamily) : Prop :=
  ∃ S : YM4IRSystem R, Nonempty (YM4IRUniformStrong S)

structure YM4LimitSemantics (R : YM4RegulatedGapFamily) where
  order : YM4LimitOrder
  agreesWithRegime : order = R.regime.limitOrder

def YM4_B6_HARDENED_OPEN_MATH : Prop :=
  ∃ R : YM4RegulatedGapFamily,
    Nonempty (YM4UniformPhysicalLowerBound R) ∧
    YM4D_uniform_IR_mass_gap_producer R ∧
    Nonempty (YM4LimitSemantics R)

end MCore.YangMills.A1
