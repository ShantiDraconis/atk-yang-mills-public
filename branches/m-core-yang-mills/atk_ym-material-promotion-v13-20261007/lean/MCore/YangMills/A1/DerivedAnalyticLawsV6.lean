import MCore.YangMills.A1.CanonicalSameModelBundleV5

namespace MCore.YangMills.A1

/-- The regulated L2 norm-square is nonnegative because it is the integral of
a pointwise nonnegative squared norm. -/
theorem regulatedNormSq_nonneg
    {C : RegulatedYM4Construction}
    {a : C.Signature.Regulator}
    {L : C.Signature.Volume}
    (ψ : RegulatedL2Vector C a L) :
    0 ≤ regulatedNormSq ψ := by
  unfold regulatedNormSq
  exact MeasureTheory.integral_nonneg (fun x => by positivity)

/-- n-fold transfer evolution on one fixed regulator/volume fiber. -/
def transferIterate
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    (B4 : PositiveTransferDataV2 C P)
    (a : C.Signature.Regulator)
    (L : C.Signature.Volume) :
    Nat → RegulatedL2Vector C a L → RegulatedL2Vector C a L
  | 0, ψ => ψ
  | n + 1, ψ => B4.transferOp a L (transferIterate B4 a L n ψ)

@[simp] theorem transferIterate_zero
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    (B4 : PositiveTransferDataV2 C P)
    (a : C.Signature.Regulator)
    (L : C.Signature.Volume)
    (ψ : RegulatedL2Vector C a L) :
    transferIterate B4 a L 0 ψ = ψ :=
  rfl

@[simp] theorem transferIterate_succ
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    (B4 : PositiveTransferDataV2 C P)
    (a : C.Signature.Regulator)
    (L : C.Signature.Volume)
    (n : Nat)
    (ψ : RegulatedL2Vector C a L) :
    transferIterate B4 a L (n + 1) ψ =
      B4.transferOp a L (transferIterate B4 a L n ψ) :=
  rfl

/-- The B4 contraction law propagates to every finite transfer iterate. -/
theorem transferIterate_norm_nonincreasing
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    (B4 : PositiveTransferDataV2 C P)
    (a : C.Signature.Regulator)
    (L : C.Signature.Volume)
    (n : Nat)
    (ψ : RegulatedL2Vector C a L) :
    regulatedNormSq (transferIterate B4 a L n ψ) ≤
      regulatedNormSq ψ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        regulatedNormSq (transferIterate B4 a L (n + 1) ψ)
            = regulatedNormSq
                (B4.transferOp a L (transferIterate B4 a L n ψ)) := rfl
        _ ≤ regulatedNormSq (transferIterate B4 a L n ψ) :=
          B4.h_contraction a L (transferIterate B4 a L n ψ)
        _ ≤ regulatedNormSq ψ := ih

/-- Fixed uniform decay factor supplied by the already-proved positive V2 mass
scale. This is a definition, not a new hypothesis. -/
noncomputable def uniformDecayFactor
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P}
    (U : UniformRegulatorControlV2 C P B3 B4)
    (a : C.Signature.Regulator) : ℝ :=
  Real.exp (-P.cutoffValue a * U.m0)

/-- The uniform decay factor is always strictly positive. -/
theorem uniformDecayFactor_pos
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P}
    (U : UniformRegulatorControlV2 C P B3 B4)
    (a : C.Signature.Regulator) :
    0 < uniformDecayFactor U a := by
  exact Real.exp_pos _

/-- At every strictly positive cutoff the positive physical mass makes the
uniform decay factor strictly smaller than one. -/
theorem uniformDecayFactor_lt_one
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P}
    (U : UniformRegulatorControlV2 C P B3 B4)
    {a : C.Signature.Regulator}
    (hcutPos : 0 < P.cutoffValue a) :
    uniformDecayFactor U a < 1 := by
  unfold uniformDecayFactor
  calc
    Real.exp (-P.cutoffValue a * U.m0) < Real.exp 0 := by
      apply Real.exp_lt_exp.mpr
      nlinarith [U.hm0]
    _ = 1 := Real.exp_zero

/-- Main V6 analytic law: on the vacuum-orthogonal sector, the exact B4
one-step transfer estimate is controlled by the fixed positive mass m0,
uniformly over every admissible sufficiently small cutoff. -/
theorem uniform_v2_transfer_decay_at_mass
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P}
    (U : UniformRegulatorControlV2 C P B3 B4)
    {a : C.Signature.Regulator}
    {L : C.Signature.Volume}
    (hadm : C.admissible a L)
    (hcutPos : 0 < P.cutoffValue a)
    (hcutLt : P.cutoffValue a < U.a0)
    (ψ : RegulatedL2Vector C a L)
    (horth : regulatedInner ψ (B4.vacuum a L) = 0) :
    regulatedNormSq (B4.transferOp a L ψ) ≤
      uniformDecayFactor U a * regulatedNormSq ψ := by
  calc
    regulatedNormSq (B4.transferOp a L ψ)
        ≤ Real.exp (-P.cutoffValue a * B4.spectralGap a L) *
            regulatedNormSq ψ :=
      B4.h_spectral_gap_controls_transfer a L ψ horth
    _ ≤ Real.exp (-P.cutoffValue a * U.m0) *
          regulatedNormSq ψ := by
      exact mul_le_mul_of_nonneg_right
        (uniform_v2_exp_gap_le_mass U hadm hcutPos hcutLt)
        (regulatedNormSq_nonneg ψ)
    _ = uniformDecayFactor U a * regulatedNormSq ψ := rfl

/-- A compact theorem bundle for the algebraic/analytic consequences already
derived from V3. It contains no open mathematical proposition. -/
structure DerivedAnalyticLawsV6
    (C : RegulatedYM4Construction)
    (W : A1MaterialWitnessV3 C) : Prop where
  massPositive : 0 < W.uniformMass.m0
  massNonzero : W.uniformMass.m0 ≠ 0
  gapNotIdenticallyZero :
    ¬ (∀ a L, W.uniformMass.gapAt a L = 0)

theorem derivedAnalyticLawsV6
    {C : RegulatedYM4Construction}
    (W : A1MaterialWitnessV3 C) :
    DerivedAnalyticLawsV6 C W where
  massPositive := W.uniformMass.hm0
  massNonzero := uniform_v2_mass_nonzero W.uniformMass
  gapNotIdenticallyZero :=
    uniform_v2_gap_not_identically_zero W.uniformMass

#print axioms MCore.YangMills.A1.regulatedNormSq_nonneg
#print axioms MCore.YangMills.A1.transferIterate_norm_nonincreasing
#print axioms MCore.YangMills.A1.uniformDecayFactor_lt_one
#print axioms MCore.YangMills.A1.uniform_v2_transfer_decay_at_mass
#print axioms MCore.YangMills.A1.derivedAnalyticLawsV6

end MCore.YangMills.A1
