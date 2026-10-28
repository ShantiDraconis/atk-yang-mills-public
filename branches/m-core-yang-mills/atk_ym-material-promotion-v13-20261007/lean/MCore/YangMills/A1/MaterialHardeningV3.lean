import MCore.YangMills.A1.HardeningV2

namespace MCore.YangMills.A1

/--
Non-vacuum spectral witness on the same regulated L2 space used by B4 v2.

The positive norm and vacuum-orthogonality requirements rule out the
one-dimensional/vacuous sector collapse used by the current-model
counterexample.  This still does not construct physical Yang--Mills data:
the witness must be supplied from the same regulated construction C.
-/
structure RegulatedNonvacuumExcitation
    (C : RegulatedYM4Construction)
    (P : A1PhysicalData C)
    (B4 : PositiveTransferDataV2 C P) where
  regulator : C.Signature.Regulator
  volume : C.Signature.Volume
  admissible : C.admissible regulator volume
  state : RegulatedL2Vector C regulator volume
  positiveNorm : 0 < regulatedNormSq state
  orthogonalVacuum :
    regulatedInner state (B4.vacuum regulator volume) = 0

/--
Materially hardened A1 witness.

It contains:
- exact regulated construction binding;
- reflection positivity on the same regulated measure;
- transfer operator built from the same regulated action kernel;
- a positive uniform physical mass scale;
- an actual non-vacuum, positive-norm excitation orthogonal to the vacuum.

Unlike the abstract B60 carrier, this object cannot be inhabited by the
existing Unit-state trivial-model collapse without violating positiveNorm.
-/
structure A1MaterialWitnessV3 (C : RegulatedYM4Construction) where
  physicalData : A1PhysicalData C
  measureInvariance : MeasureInvariance C
  observableInvariance : ObservableInvariance C
  reflectionPositivity :
    ReflectionPositivityDataV2 C physicalData
  positiveTransfer :
    PositiveTransferDataV2 C physicalData
  uniformMass :
    UniformRegulatorControlV2
      C physicalData reflectionPositivity positiveTransfer
  excitation :
    RegulatedNonvacuumExcitation C physicalData positiveTransfer

def A1MaterialOpenMathV3 (C : RegulatedYM4Construction) : Prop :=
  Nonempty (A1MaterialWitnessV3 C)

/-- Forgetting only the non-vacuum excitation recovers the v2 scientific
witness.  Hence v3 is a genuine strengthening of the existing hardening. -/
def A1MaterialWitnessV3.toV2
    {C : RegulatedYM4Construction}
    (W : A1MaterialWitnessV3 C) :
    A1ScientificWitnessV2 C where
  physicalData := W.physicalData
  measureInvariance := W.measureInvariance
  observableInvariance := W.observableInvariance
  reflectionPositivity := W.reflectionPositivity
  positiveTransfer := W.positiveTransfer
  uniformMass := W.uniformMass

theorem a1_material_v3_implies_v2
    {C : RegulatedYM4Construction}
    (h : A1MaterialOpenMathV3 C) :
    A1ScientificOpenBridgeV2 C := by
  rcases h with ⟨W⟩
  exact ⟨W.toV2⟩

/-- Positive physical mass scale is an immediate law of every material v3
witness. -/
theorem a1_material_v3_positive_mass
    {C : RegulatedYM4Construction}
    (W : A1MaterialWitnessV3 C) :
    0 < W.uniformMass.m0 :=
  W.uniformMass.hm0

/-- Every material v3 witness contains a genuinely nonzero regulated state. -/
theorem a1_material_v3_nonzero_excitation
    {C : RegulatedYM4Construction}
    (W : A1MaterialWitnessV3 C) :
    0 < regulatedNormSq W.excitation.state :=
  W.excitation.positiveNorm

#print axioms MCore.YangMills.A1.a1_material_v3_implies_v2
#print axioms MCore.YangMills.A1.a1_material_v3_positive_mass
#print axioms MCore.YangMills.A1.a1_material_v3_nonzero_excitation

end MCore.YangMills.A1
