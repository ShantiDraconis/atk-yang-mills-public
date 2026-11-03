import MCore.YangMills.QCore

/-!
Formal dynamics and balance laws for the YM multistate Q-core.

These are abstract algebraic/dynamical definitions. No theorem in this file
identifies the model with four-dimensional Yang--Mills theory.
-/

namespace MCore.YangMills.QDynamics

open MCore.YangMills.QCore

structure Profile where
  contraction : Nat
  tension : Nat
  repulsion : Nat
  deriving DecidableEq, Repr

/-- Exact balance of inward and outward components. -/
def CriticalBalance (p : Profile) : Prop :=
  p.contraction = p.repulsion

/-- A balanced profile can remain at the distinguished Q state. -/
def step (p : Profile) (s : YMState) : YMState :=
  match s with
  | .qCore =>
      if p.contraction = p.repulsion then I00
      else if p.contraction > p.repulsion then .qCore
      else if p.tension % 2 = 0 then .proofSector else .refutationSector
  | .proofSector =>
      if p.contraction > p.repulsion then I00 else .proofSector
  | .refutationSector =>
      if p.contraction > p.repulsion then I00 else .refutationSector

theorem criticalBalance_fixed (p : Profile) (h : CriticalBalance p) :
    step p I00 = I00 := by
  simp [step, CriticalBalance, h]

theorem contraction_returns_proof (p : Profile)
    (h : p.contraction > p.repulsion) :
    step p YMState.proofSector = I00 := by
  simp [step, h]

theorem contraction_returns_refutation (p : Profile)
    (h : p.contraction > p.repulsion) :
    step p YMState.refutationSector = I00 := by
  simp [step, h]

/-- Q is a stopping point exactly in the model-internal fixed-point sense. -/
def StopsAtQ (p : Profile) : Prop := step p I00 = I00

theorem criticalBalance_stops (p : Profile) (h : CriticalBalance p) :
    StopsAtQ p :=
  criticalBalance_fixed p h

/-- Resolution is explicitly reversible through the Q core. -/
theorem proof_Q_proof :
    resolveProof (returnToCore YMState.proofSector) = YMState.proofSector :=
  proof_roundtrip

theorem refutation_Q_refutation :
    resolveRefutation (returnToCore YMState.refutationSector) =
      YMState.refutationSector :=
  refutation_roundtrip

/-- Scientific bridge remains an explicit proposition, not an assumed inhabitant. -/
structure PhysicalInterpretation (PhysicalState : Type) where
  interpret : YMState → PhysicalState

def PhysicalBridgeExists : Prop :=
  ∃ (PhysicalState : Type), Nonempty (PhysicalInterpretation PhysicalState)

end MCore.YangMills.QDynamics
