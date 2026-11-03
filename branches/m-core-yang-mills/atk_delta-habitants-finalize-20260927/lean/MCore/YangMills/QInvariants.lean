import MCore.YangMills.QDynamics

/-!
Quantitative invariants, resolution conditions, and balance characterization
for the abstract Q-core. This remains model-internal and carries no physical
Yang--Mills identification.
-/

namespace MCore.YangMills.QInvariants

open MCore.YangMills.QCore
open MCore.YangMills.QDynamics

def imbalance (p : Profile) : Int :=
  Int.ofNat p.contraction - Int.ofNat p.repulsion

def Balanced (p : Profile) : Prop := imbalance p = 0

theorem balanced_iff_critical (p : Profile) :
    Balanced p ↔ CriticalBalance p := by
  simp [Balanced, imbalance, CriticalBalance]

inductive Resolution where
  | proof
  | core
  | refutation
  deriving DecidableEq, Repr

def resolution (p : Profile) : Resolution :=
  if p.contraction = p.repulsion then .core
  else if p.contraction > p.repulsion then .core
  else if p.tension % 2 = 0 then .proof else .refutation

theorem critical_resolves_core (p : Profile) (h : CriticalBalance p) :
    resolution p = .core := by
  simp [resolution, CriticalBalance, h]

theorem balanced_stops_at_Q (p : Profile) (h : Balanced p) :
    StopsAtQ p := by
  exact criticalBalance_stops p ((balanced_iff_critical p).mp h)

def resolveState : Resolution → YMState
  | .proof => .proofSector
  | .core => I00
  | .refutation => .refutationSector

theorem critical_state_is_I00 (p : Profile) (h : CriticalBalance p) :
    resolveState (resolution p) = I00 := by
  simp [resolution, resolveState, CriticalBalance, h]

theorem proof_sector_roundtrip :
    resolveProof (returnToCore YMState.proofSector) = YMState.proofSector :=
  proof_roundtrip

theorem refutation_sector_roundtrip :
    resolveRefutation (returnToCore YMState.refutationSector) =
      YMState.refutationSector :=
  refutation_roundtrip

/-- A quantitative potential measuring absolute contraction/repulsion imbalance. -/
def imbalanceMagnitude (p : Profile) : Nat :=
  if p.contraction ≥ p.repulsion
  then p.contraction - p.repulsion
  else p.repulsion - p.contraction

theorem critical_zero_magnitude (p : Profile) (h : CriticalBalance p) :
    imbalanceMagnitude p = 0 := by
  simp [imbalanceMagnitude, CriticalBalance] at *
  omega

theorem zero_magnitude_critical (p : Profile)
    (h : imbalanceMagnitude p = 0) :
    CriticalBalance p := by
  simp [imbalanceMagnitude, CriticalBalance] at *
  omega

theorem critical_iff_zero_magnitude (p : Profile) :
    CriticalBalance p ↔ imbalanceMagnitude p = 0 :=
  ⟨critical_zero_magnitude p, zero_magnitude_critical p⟩

end MCore.YangMills.QInvariants
