import Std

/-!
YM Q-core: a purely formal multistate algebra.

Scientific boundary:
This file does NOT assert that this algebra models four-dimensional
Yang--Mills theory, nor that it proves or refutes the Yang--Mills mass-gap
problem. Any such claim requires a separate, nontrivial physical bridge.
-/

namespace MCore.YangMills.QCore

inductive YMState where
  | proofSector
  | qCore
  | refutationSector
  deriving DecidableEq, Repr, BEq

/-- Formal name for the distinguished indeterminate state.
    It is not division in Nat, Real, or Complex. -/
def I00 : YMState := .qCore

def resolveProof : YMState → YMState
  | .qCore => .proofSector
  | s => s

def resolveRefutation : YMState → YMState
  | .qCore => .refutationSector
  | s => s

def returnToCore : YMState → YMState
  | .proofSector => .qCore
  | .refutationSector => .qCore
  | .qCore => .qCore

/-- Contraction toward the distinguished core. -/
def contraction : YMState → YMState := returnToCore

/-- Tension preserves the currently occupied formal sector. -/
def tension : YMState → YMState := id

/-- Repulsion from the core requires a chosen resolution sector. -/
def repulsion (chooseProof : Bool) : YMState → YMState
  | .qCore => if chooseProof then .proofSector else .refutationSector
  | s => s

theorem I00_fixed :
    returnToCore I00 = I00 := rfl

theorem contraction_fixed :
    contraction I00 = I00 := rfl

theorem proof_returns_to_I00 :
    returnToCore (resolveProof I00) = I00 := rfl

theorem refutation_returns_to_I00 :
    returnToCore (resolveRefutation I00) = I00 := rfl

theorem proof_roundtrip :
    resolveProof (returnToCore YMState.proofSector) = YMState.proofSector := rfl

theorem refutation_roundtrip :
    resolveRefutation (returnToCore YMState.refutationSector) =
      YMState.refutationSector := rfl

theorem tension_I00 :
    tension I00 = I00 := rfl

theorem repulsion_true :
    repulsion true I00 = YMState.proofSector := rfl

theorem repulsion_false :
    repulsion false I00 = YMState.refutationSector := rfl

/-- The formal core is distinct from either resolved sector. -/
theorem I00_ne_proof : I00 ≠ YMState.proofSector := by
  decide

theorem I00_ne_refutation : I00 ≠ YMState.refutationSector := by
  decide

end MCore.YangMills.QCore
