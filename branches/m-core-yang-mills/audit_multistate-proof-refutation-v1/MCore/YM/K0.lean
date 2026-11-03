namespace MCore.YM

inductive NodeStatus where
  | proved
  | provedConditional
  | refuted
  | definitionInterface
  | numericalEvidence
  | openBridge
  deriving DecidableEq, Repr

structure CertNode where
  statement : Prop
  status : NodeStatus

structure ProofCertificate (n : CertNode) : Prop where
  status_proved : n.status = .proved
  proof : n.statement

def k0OpenBridge (P : Prop) : CertNode :=
  { statement := P, status := .openBridge }

theorem openBridge_not_certified (P : Prop) :
    ¬ Nonempty (ProofCertificate (k0OpenBridge P)) := by
  intro h
  rcases h with ⟨c⟩
  cases c.status_proved

end MCore.YM
