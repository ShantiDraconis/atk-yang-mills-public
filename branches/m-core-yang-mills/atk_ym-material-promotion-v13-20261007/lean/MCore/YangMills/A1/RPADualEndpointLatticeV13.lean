import MCore.YangMills.A1.RPADualConfirmationV13

namespace MCore.YangMills.A1.Final

/-!
Dual-endpoint lattice.

The free layer records multiplicities of OPEN/CLOSED endpoint positions.
The canonical layer quotients multiplicity to support, yielding four states.
No inhabitant of FINAL_ROOT is synthesized by this structural lattice.
-/

structure FreeEndpointState where
  openMultiplicity : Nat
  closedMultiplicity : Nat
deriving DecidableEq, Repr

namespace FreeEndpointState

def empty : FreeEndpointState := ⟨0, 0⟩
def openAtom : FreeEndpointState := ⟨1, 0⟩
def closedAtom : FreeEndpointState := ⟨0, 1⟩
def dual : FreeEndpointState := ⟨1, 1⟩

def add (a b : FreeEndpointState) : FreeEndpointState :=
  ⟨a.openMultiplicity + b.openMultiplicity,
   a.closedMultiplicity + b.closedMultiplicity⟩

instance : Add FreeEndpointState := ⟨add⟩

theorem open_add_open : openAtom + openAtom = ⟨2, 0⟩ := rfl
theorem closed_add_closed : closedAtom + closedAtom = ⟨0, 2⟩ := rfl
theorem open_add_closed : openAtom + closedAtom = dual := rfl
theorem closed_add_open : closedAtom + openAtom = dual := rfl
theorem two_open_one_closed : openAtom + openAtom + closedAtom = ⟨2, 1⟩ := rfl
theorem one_open_two_closed : openAtom + closedAtom + closedAtom = ⟨1, 2⟩ := rfl
theorem two_open_two_closed : openAtom + openAtom + closedAtom + closedAtom = ⟨2, 2⟩ := rfl
theorem open_open_open : openAtom + openAtom + openAtom = ⟨3, 0⟩ := rfl
theorem closed_closed_closed : closedAtom + closedAtom + closedAtom = ⟨0, 3⟩ := rfl
theorem open_open_closed : openAtom + openAtom + closedAtom = ⟨2, 1⟩ := rfl
theorem open_closed_open : openAtom + closedAtom + openAtom = ⟨2, 1⟩ := rfl
theorem closed_open_open : closedAtom + openAtom + openAtom = ⟨2, 1⟩ := rfl
theorem open_closed_closed : openAtom + closedAtom + closedAtom = ⟨1, 2⟩ := rfl
theorem closed_open_closed : closedAtom + openAtom + closedAtom = ⟨1, 2⟩ := rfl
theorem closed_closed_open : closedAtom + closedAtom + openAtom = ⟨1, 2⟩ := rfl

def fullFree : FreeEndpointState :=
  openAtom + openAtom + closedAtom + closedAtom

theorem fullFree_eq : fullFree = ⟨2, 2⟩ := rfl

end FreeEndpointState

inductive CanonicalEndpointState where
  | empty
  | openSide
  | closedSide
  | full
deriving DecidableEq, Repr

namespace CanonicalEndpointState

def hasOpen : CanonicalEndpointState → Bool
  | .empty => false
  | .openSide => true
  | .closedSide => false
  | .full => true

def hasClosed : CanonicalEndpointState → Bool
  | .empty => false
  | .openSide => false
  | .closedSide => true
  | .full => true

def ofSupport (o c : Bool) : CanonicalEndpointState :=
  match o, c with
  | false, false => .empty
  | true, false => .openSide
  | false, true => .closedSide
  | true, true => .full

def join (a b : CanonicalEndpointState) : CanonicalEndpointState :=
  ofSupport (a.hasOpen || b.hasOpen) (a.hasClosed || b.hasClosed)

instance : Add CanonicalEndpointState := ⟨join⟩

theorem open_idempotent : openSide + openSide = openSide := rfl
theorem closed_idempotent : closedSide + closedSide = closedSide := rfl
theorem open_closed_full : openSide + closedSide = full := rfl
theorem closed_open_full : closedSide + openSide = full := rfl
theorem full_open_full : full + openSide = full := rfl
theorem full_closed_full : full + closedSide = full := rfl
theorem full_idempotent : full + full = full := rfl

def normalize (s : FreeEndpointState) : CanonicalEndpointState :=
  ofSupport (s.openMultiplicity != 0) (s.closedMultiplicity != 0)

theorem normalize_empty :
    normalize FreeEndpointState.empty = empty := rfl
theorem normalize_open :
    normalize FreeEndpointState.openAtom = openSide := rfl
theorem normalize_closed :
    normalize FreeEndpointState.closedAtom = closedSide := rfl
theorem normalize_dual :
    normalize FreeEndpointState.dual = full := rfl
theorem normalize_two_open_two_closed :
    normalize ⟨2, 2⟩ = full := rfl

theorem open_open_open_normalizes :
    openSide + openSide + openSide = openSide := rfl
theorem closed_closed_closed_normalizes :
    closedSide + closedSide + closedSide = closedSide := rfl
theorem open_open_closed_full :
    openSide + openSide + closedSide = full := rfl
theorem open_closed_open_full :
    openSide + closedSide + openSide = full := rfl
theorem closed_open_open_full :
    closedSide + openSide + openSide = full := rfl
theorem open_closed_closed_full :
    openSide + closedSide + closedSide = full := rfl
theorem closed_open_closed_full :
    closedSide + openSide + closedSide = full := rfl
theorem closed_closed_open_full :
    closedSide + closedSide + openSide = full := rfl
theorem open_open_closed_closed_full :
    openSide + openSide + closedSide + closedSide = full := rfl

theorem normalize_closed_open :
    normalize (FreeEndpointState.closedAtom + FreeEndpointState.openAtom) = full := rfl
theorem normalize_open_open_open :
    normalize (FreeEndpointState.openAtom + FreeEndpointState.openAtom + FreeEndpointState.openAtom) = openSide := rfl
theorem normalize_closed_closed_closed :
    normalize (FreeEndpointState.closedAtom + FreeEndpointState.closedAtom + FreeEndpointState.closedAtom) = closedSide := rfl
theorem normalize_open_open_closed :
    normalize (FreeEndpointState.openAtom + FreeEndpointState.openAtom + FreeEndpointState.closedAtom) = full := rfl
theorem normalize_open_closed_open :
    normalize (FreeEndpointState.openAtom + FreeEndpointState.closedAtom + FreeEndpointState.openAtom) = full := rfl
theorem normalize_closed_open_open :
    normalize (FreeEndpointState.closedAtom + FreeEndpointState.openAtom + FreeEndpointState.openAtom) = full := rfl
theorem normalize_open_closed_closed :
    normalize (FreeEndpointState.openAtom + FreeEndpointState.closedAtom + FreeEndpointState.closedAtom) = full := rfl
theorem normalize_closed_open_closed :
    normalize (FreeEndpointState.closedAtom + FreeEndpointState.openAtom + FreeEndpointState.closedAtom) = full := rfl
theorem normalize_closed_closed_open :
    normalize (FreeEndpointState.closedAtom + FreeEndpointState.closedAtom + FreeEndpointState.openAtom) = full := rfl
theorem normalize_fullFree :
    normalize FreeEndpointState.fullFree = full := rfl

structure CubeUpTo3Certificate : Prop where
  open1 : normalize FreeEndpointState.openAtom = openSide
  closed1 : normalize FreeEndpointState.closedAtom = closedSide
  openClosed2 : normalize (FreeEndpointState.openAtom + FreeEndpointState.closedAtom) = full
  closedOpen2 : normalize (FreeEndpointState.closedAtom + FreeEndpointState.openAtom) = full
  openOpen2 : normalize (FreeEndpointState.openAtom + FreeEndpointState.openAtom) = openSide
  closedClosed2 : normalize (FreeEndpointState.closedAtom + FreeEndpointState.closedAtom) = closedSide
  openOpenOpen3 : normalize (FreeEndpointState.openAtom + FreeEndpointState.openAtom + FreeEndpointState.openAtom) = openSide
  closedClosedClosed3 : normalize (FreeEndpointState.closedAtom + FreeEndpointState.closedAtom + FreeEndpointState.closedAtom) = closedSide
  openOpenClosed3 : normalize (FreeEndpointState.openAtom + FreeEndpointState.openAtom + FreeEndpointState.closedAtom) = full
  openClosedOpen3 : normalize (FreeEndpointState.openAtom + FreeEndpointState.closedAtom + FreeEndpointState.openAtom) = full
  closedOpenOpen3 : normalize (FreeEndpointState.closedAtom + FreeEndpointState.openAtom + FreeEndpointState.openAtom) = full
  openClosedClosed3 : normalize (FreeEndpointState.openAtom + FreeEndpointState.closedAtom + FreeEndpointState.closedAtom) = full
  closedOpenClosed3 : normalize (FreeEndpointState.closedAtom + FreeEndpointState.openAtom + FreeEndpointState.closedAtom) = full
  closedClosedOpen3 : normalize (FreeEndpointState.closedAtom + FreeEndpointState.closedAtom + FreeEndpointState.openAtom) = full

def cubeUpTo3Certificate : CubeUpTo3Certificate where
  open1 := rfl
  closed1 := rfl
  openClosed2 := rfl
  closedOpen2 := rfl
  openOpen2 := rfl
  closedClosed2 := rfl
  openOpenOpen3 := rfl
  closedClosedClosed3 := rfl
  openOpenClosed3 := rfl
  openClosedOpen3 := rfl
  closedOpenOpen3 := rfl
  openClosedClosed3 := rfl
  closedOpenClosed3 := rfl
  closedClosedOpen3 := rfl

theorem CUBE_UP_TO_3_CLOSED :
    Nonempty CubeUpTo3Certificate :=
  ⟨cubeUpTo3Certificate⟩

end CanonicalEndpointState

def FullEndpointPayload
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  OPEN_ENDPOINT D H G ∧ CLOSED_ENDPOINT D H G

theorem fullEndpointPayload_iff_dualEndpointState
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    FullEndpointPayload D H G ↔ DualEndpointState D H G := by
  constructor
  · rintro ⟨ho, hc⟩
    exact ⟨ho, hc, openEndpoint_iff_closedEndpoint⟩
  · intro S
    exact ⟨S.openEndpoint, S.closedEndpoint⟩

theorem fullEndpointPayload_iff_finalRoot
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D} :
    FullEndpointPayload D H G ↔ FINAL_ROOT D H G := by
  constructor
  · rintro ⟨ho, _⟩
    exact ho
  · intro h
    exact ⟨h, h⟩

theorem globalExternalCertificate_to_fullEndpointPayload
    {C : RegulatedYM4Construction}
    {F : K20ScientificFrontier}
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    {O : K30SpectralTransferObligations F D H G}
    (E : FinalExternalCertificate C F D H G O) :
    FullEndpointPayload D H G := by
  have hroot := finalExternal_to_FINAL_ROOT E
  exact ⟨hroot, hroot⟩

#print axioms MCore.YangMills.A1.Final.FreeEndpointState.closed_add_open
#print axioms MCore.YangMills.A1.Final.FreeEndpointState.open_open_open
#print axioms MCore.YangMills.A1.Final.FreeEndpointState.closed_closed_closed
#print axioms MCore.YangMills.A1.Final.CanonicalEndpointState.CUBE_UP_TO_3_CLOSED
#print axioms MCore.YangMills.A1.Final.CanonicalEndpointState.normalize_fullFree
#print axioms MCore.YangMills.A1.Final.FreeEndpointState.open_add_open
#print axioms MCore.YangMills.A1.Final.CanonicalEndpointState.open_idempotent
#print axioms MCore.YangMills.A1.Final.CanonicalEndpointState.open_closed_full
#print axioms MCore.YangMills.A1.Final.CanonicalEndpointState.normalize_dual
#print axioms MCore.YangMills.A1.Final.fullEndpointPayload_iff_dualEndpointState
#print axioms MCore.YangMills.A1.Final.fullEndpointPayload_iff_finalRoot
#print axioms MCore.YangMills.A1.Final.globalExternalCertificate_to_fullEndpointPayload

end MCore.YangMills.A1.Final
