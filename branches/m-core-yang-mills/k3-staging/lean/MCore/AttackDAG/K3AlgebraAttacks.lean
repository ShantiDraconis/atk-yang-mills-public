import MCore.K3

namespace MCore

def k3_attack_route_only : Prop := k3_gap.disposition = .openBridge

theorem k3_attack_route_only_holds : k3_attack_route_only := rfl

theorem k3_attack_cannot_promote : ¬ Nonempty (ProofCertificate k3_gap_node) :=
  k3_gap_not_certified

end MCore
