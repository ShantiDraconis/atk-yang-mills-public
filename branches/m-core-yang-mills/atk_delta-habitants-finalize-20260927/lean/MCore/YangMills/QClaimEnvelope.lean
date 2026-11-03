import MCore.YangMills.QClaimTests

/-!
Yang--Mills adaptation of the useful P-vs-NP claim-envelope pattern.

Provenance/research source:
m-core-p-vs-np: PvsNPOpenMath, PNP_RESIDUE, ORIENTED_WITNESS_BOUNDARY.
No theorem or certificate is imported cross-repository; the logic is re-derived
locally as required by ATK repository isolation.

This closes only the structural claim envelope. It does not orient the
Yang--Mills scientific endpoint.
-/

namespace MCore.YangMills.QClaimEnvelope

/-- Three candidate orientations of the local multistate research envelope. -/
inductive Orientation where
  | proof
  | core
  | refutation
  deriving DecidableEq, Repr

structure OrientedEvidence where
  orientation : Orientation
  material : Prop

def ProofOrientation (e : OrientedEvidence) : Prop :=
  e.orientation = .proof ∧ e.material

def CoreOrientation (e : OrientedEvidence) : Prop :=
  e.orientation = .core ∧ e.material

def RefutationOrientation (e : OrientedEvidence) : Prop :=
  e.orientation = .refutation ∧ e.material

/-- Structural envelope: an evidence package has exactly one constructor-level
orientation, but its material proposition still has to be proved independently. -/
def StructuralEnvelope (e : OrientedEvidence) : Prop :=
  e.orientation = .proof ∨ e.orientation = .core ∨ e.orientation = .refutation

theorem structural_envelope_closed (e : OrientedEvidence) :
    StructuralEnvelope e := by
  cases e.orientation <;> simp [StructuralEnvelope]

theorem proof_refutation_exclusive (e : OrientedEvidence) :
    ¬ (ProofOrientation e ∧ RefutationOrientation e) := by
  simp [ProofOrientation, RefutationOrientation]

theorem proof_core_exclusive (e : OrientedEvidence) :
    ¬ (ProofOrientation e ∧ CoreOrientation e) := by
  simp [ProofOrientation, CoreOrientation]

theorem core_refutation_exclusive (e : OrientedEvidence) :
    ¬ (CoreOrientation e ∧ RefutationOrientation e) := by
  simp [CoreOrientation, RefutationOrientation]

/-- Material producers are deliberately separated from structural orientation. -/
structure MaterialProducers where
  endpointTyped : Prop
  genuine4D : Prop
  continuumIR : Prop
  spectralTransfer : Prop
  positiveUniformGap : Prop
  qPhysicalSemantics : Prop

def ProofMaterial (p : MaterialProducers) : Prop :=
  p.endpointTyped ∧ p.genuine4D ∧ p.continuumIR ∧
  p.spectralTransfer ∧ p.positiveUniformGap

def CoreMaterial (p : MaterialProducers) : Prop :=
  p.endpointTyped ∧ p.genuine4D ∧ p.continuumIR ∧
  p.spectralTransfer ∧ p.qPhysicalSemantics

/-- The refutation lane needs an actual contradictory physical consequence,
not merely failure to construct ProofMaterial. -/
def RefutationMaterial (p : MaterialProducers) (contradiction : Prop) : Prop :=
  p.endpointTyped ∧ p.genuine4D ∧ contradiction

/-- Structural closure cannot manufacture any material producer. -/
theorem envelope_does_not_supply_material
    (e : OrientedEvidence) (h : StructuralEnvelope e) :
    StructuralEnvelope e := h

end MCore.YangMills.QClaimEnvelope
