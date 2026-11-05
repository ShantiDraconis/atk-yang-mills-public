import MCore.K1

namespace MCore

/-- K2 certificate node: status and proposition are coupled in one typed object. -/
structure CertNode where
  status : SignatureStatus
  statement : Prop

/-- A proof certificate can only be constructed for a node whose status is provedProperty. -/
structure ProofCertificate (n : CertNode) where
  status_proved : n.status = .provedProperty
  proof : n.statement

/-- K1 lifted into K2 without inventing a scientific statement: this node records the
    already-certified structural fact that the K1 target is an open bridge. -/
def k1_node : CertNode :=
  { status := k1Target.status
    statement := k1Target.status = .openBridge }

theorem k2_node_status_openBridge : k1_node.status = .openBridge := by
  exact k1_status_openBridge

theorem k2_node_not_proved : k1_node.status ≠ .provedProperty := by
  simpa [k1_node] using k1_not_proved

/-- Core K2 firewall: an OPEN_BRIDGE K1 node has no ProofCertificate. -/
theorem bridge_not_certified : ¬ Nonempty (ProofCertificate k1_node) := by
  intro h
  rcases h with ⟨c⟩
  exact k2_node_not_proved c.status_proved

end MCore
