import MCore.K6
import MCore.YM.K0

namespace MCore.Audit8x5

inductive AxisState where
  | matched | blocking | refuted | external | pending
  deriving DecidableEq, Repr

structure Sigma5 where
  HC : AxisState
  Q : AxisState
  S : AxisState
  K : AxisState
  A : AxisState
  deriving Repr

/-- Before a literal official endpoint is typed, semantic matching axes cannot
    be promoted. -/
def sigma0 : Sigma5 :=
  { HC := .pending, Q := .pending, S := .pending, K := .pending, A := .pending }

theorem no_placebo_generic :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k6_target_not_certified

theorem no_placebo_legacy (P : Prop) :
    ¬ Nonempty (ProofCertificate (YM.k0OpenBridge P)) :=
  YM.openBridge_not_certified P


theorem HC_pending : sigma0.HC = .pending := rfl
theorem Q_pending : sigma0.Q = .pending := rfl
theorem S_pending : sigma0.S = .pending := rfl
theorem K_pending : sigma0.K = .pending := rfl
theorem A_pending : sigma0.A = .pending := rfl

#print axioms no_placebo_generic
#print axioms no_placebo_legacy

end MCore.Audit8x5
