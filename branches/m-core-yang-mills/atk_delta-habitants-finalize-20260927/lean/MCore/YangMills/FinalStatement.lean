import MCore.YangMills.QClaimEnvelope

/-!
Dense typed scientific endpoint for the Yang--Mills research line.

This file TYPES the target and its dependencies. It does not inhabit the target.
The spectral gap is represented only after a Hamiltonian/vacuum/spectrum package
has been supplied. No quotient or I00 interpretation is inserted into the
spectral definition.
-/

namespace MCore.YangMills.FinalStatement

/-- Minimal abstract carrier for a rigorously constructed 4D quantum YM theory.
Concrete producers must instantiate this with the repository's genuine objects. -/
structure QuantumYM4D where
  State : Type
  Hamiltonian : Type
  Energy : Type
  Spectrum : Type
  vacuum : State
  H : Hamiltonian
  energy : State → Energy
  spectrum : Spectrum

/-- Semantic laws are deliberately propositions to be proved by a producer,
rather than fields containing fabricated witnesses. -/
structure YM4DLaws (Y : QuantumYM4D) where
  constructionValid : Prop
  fourDimensional : Prop
  quantumYangMills : Prop
  continuumLimit : Prop
  infraredControl : Prop
  vacuumValid : Prop
  hamiltonianSelfAdjoint : Prop
  spectrumWellDefined : Prop

/-- Spectral data needed to state a positive mass gap without pretending that
the spectrum has already been constructed. -/
structure SpectralGapData (Y : QuantumYM4D) where
  gap : Nat
  vacuumEnergy : Nat
  firstExcitedEnergy : Nat

def PositiveGap {Y : QuantumYM4D} (g : SpectralGapData Y) : Prop :=
  0 < g.gap ∧ g.firstExcitedEnergy = g.vacuumEnergy + g.gap

/-- Transfer certifies that the reported gap belongs to the Hamiltonian/spectrum
of the same physical realization. Its material content remains explicit. -/
structure SpectralTransfer (Y : QuantumYM4D) (g : SpectralGapData Y) where
  sameHamiltonian : Prop
  sameSpectrum : Prop
  vacuumIsGroundState : Prop
  firstExcitationCertified : Prop

/-- Exact typed endpoint used by all three claim lanes. -/
def YangMillsExistenceMassGap : Prop :=
  ∃ (Y : QuantumYM4D),
    ∃ (laws : YM4DLaws Y),
      laws.constructionValid ∧
      laws.fourDimensional ∧
      laws.quantumYangMills ∧
      laws.continuumLimit ∧
      laws.infraredControl ∧
      laws.vacuumValid ∧
      laws.hamiltonianSelfAdjoint ∧
      laws.spectrumWellDefined ∧
      ∃ (g : SpectralGapData Y),
        PositiveGap g ∧
        ∃ (tr : SpectralTransfer Y g),
          tr.sameHamiltonian ∧
          tr.sameSpectrum ∧
          tr.vacuumIsGroundState ∧
          tr.firstExcitationCertified

/-- A proof lane must inhabit the exact endpoint. -/
def ProofLaneTarget : Prop := YangMillsExistenceMassGap

/-- A refutation lane must prove the negation of the same endpoint. -/
def RefutationLaneTarget : Prop := ¬ YangMillsExistenceMassGap

/-- The Q lane is not silently identified with either orientation. It requires
a physical realization plus an explicit interpretation predicate. -/
def QPhysicalTarget : Prop :=
  ∃ (Y : QuantumYM4D), ∃ (_laws : YM4DLaws Y),
    ∃ (interpretI00 : Y.State → Prop), ∃ s : Y.State, interpretI00 s

/-- Closed logical envelope; excluded middle does not orient the scientific claim. -/
theorem endpoint_envelope :
    ProofLaneTarget ∨ RefutationLaneTarget := by
  exact Classical.em YangMillsExistenceMassGap

theorem proof_refutation_exclusive :
    ¬ (ProofLaneTarget ∧ RefutationLaneTarget) := by
  simp [ProofLaneTarget, RefutationLaneTarget]

end MCore.YangMills.FinalStatement
