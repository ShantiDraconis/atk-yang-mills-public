import MCore.K1

namespace MCore.BackwardAudit

/-- The repository currently types the mass-gap research route and its status,
    but not the full Yang--Mills existence + positive mass-gap proposition. -/
def endpointPropositionTyped : Bool := false

def endpointTypeResidue : String :=
  "TYPE_ENDPOINT_RESIDUE: K1 records massGap/openBridge but no final Yang-Mills proposition is typed."

theorem endpoint_route_is_massGap :
    k1Target.route = .massGap := by rfl

theorem endpoint_proposition_still_untyped :
    endpointPropositionTyped = false := by rfl

#print axioms MCore.BackwardAudit.endpoint_route_is_massGap
#print axioms MCore.BackwardAudit.endpoint_proposition_still_untyped

end MCore.BackwardAudit
