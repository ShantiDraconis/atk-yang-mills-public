import MCore.K1

namespace MCore

/-- Authoritative material-status sentinel. We deliberately do not invent a
    fake Yang--Mills endpoint type merely to make a producer probe typecheck. -/
def YangMillsCanonicalEndpointTyped : Bool := false

theorem yangMillsCanonicalEndpoint_type_residue :
    YangMillsCanonicalEndpointTyped = false := rfl

end MCore
