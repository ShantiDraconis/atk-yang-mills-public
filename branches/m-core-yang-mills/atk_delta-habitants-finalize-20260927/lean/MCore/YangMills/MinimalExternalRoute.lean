import MCore.YangMills.FinalStatement

/-!
Shortest fail-closed route from the typed Yang--Mills endpoint to a final
mathematical producer.

Instead of adding intermediate wrappers, this file compresses all material
obligations into one kernel-visible certificate.  Inhabiting this structure is
exactly the remaining mathematical task for the proof orientation.
-/

namespace MCore.YangMills.MinimalExternalRoute

open MCore.YangMills.FinalStatement

/-- One material producer carrying every obligation needed by the typed endpoint. -/
structure LiveYMProducer where
  Y : QuantumYM4D
  laws : YM4DLaws Y
  constructionValid : laws.constructionValid
  fourDimensional : laws.fourDimensional
  quantumYangMills : laws.quantumYangMills
  continuumLimit : laws.continuumLimit
  infraredControl : laws.infraredControl
  vacuumValid : laws.vacuumValid
  hamiltonianSelfAdjoint : laws.hamiltonianSelfAdjoint
  spectrumWellDefined : laws.spectrumWellDefined
  gap : SpectralGapData Y
  positiveGap : PositiveGap gap
  transfer : SpectralTransfer Y gap
  sameHamiltonian : transfer.sameHamiltonian
  sameSpectrum : transfer.sameSpectrum
  vacuumIsGroundState : transfer.vacuumIsGroundState
  firstExcitationCertified : transfer.firstExcitationCertified

/-- A single live producer closes the proof-oriented scientific endpoint. -/
theorem liveProducer_closes_endpoint
    (p : LiveYMProducer) : YangMillsExistenceMassGap := by
  refine ⟨p.Y, p.laws, p.constructionValid, p.fourDimensional,
    p.quantumYangMills, p.continuumLimit, p.infraredControl,
    p.vacuumValid, p.hamiltonianSelfAdjoint, p.spectrumWellDefined,
    p.gap, p.positiveGap, p.transfer, p.sameHamiltonian,
    p.sameSpectrum, p.vacuumIsGroundState, p.firstExcitationCertified⟩

/-- The alternative orientation must attack exactly the same endpoint. -/
def LiveYMRefutation : Prop := ¬ YangMillsExistenceMassGap

/-- Minimal terminal input: either a real producer or a proof of the exact
negation.  This is a type, not evidence that either side is inhabited. -/
inductive TerminalMaterial where
  | proof (producer : LiveYMProducer)
  | refutation (counterproof : LiveYMRefutation)

def TerminalClaim (m : TerminalMaterial) : Prop :=
  match m with
  | .proof _ => YangMillsExistenceMassGap
  | .refutation _ => ¬ YangMillsExistenceMassGap

theorem terminal_material_closes (m : TerminalMaterial) : TerminalClaim m := by
  cases m with
  | proof p => exact liveProducer_closes_endpoint p
  | refutation h => exact h

end MCore.YangMills.MinimalExternalRoute
