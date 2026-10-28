import MCore.K0

namespace MCore

/-- K1 records the research route without asserting the open mathematical target. -/
inductive ResearchRoute where
  | massGap
  | criticalLine
  | complexityLowerBound
  | cycleAlgebraicity
  | rankBridge
  | commonPrime
  deriving DecidableEq, Repr

/-- A typed K1 research target. `openBridge` is intentionally not a proof certificate. -/
structure K1Target where
  route : ResearchRoute
  status : SignatureStatus := .openBridge

/-- Yang--Mills K1: spectral mass-gap route remains an open bridge. -/
def k1Target : K1Target := ⟨.massGap, .openBridge⟩

theorem k1_status_openBridge : k1Target.status = .openBridge := rfl

theorem k1_not_proved : k1Target.status ≠ .provedProperty := by decide

end MCore
