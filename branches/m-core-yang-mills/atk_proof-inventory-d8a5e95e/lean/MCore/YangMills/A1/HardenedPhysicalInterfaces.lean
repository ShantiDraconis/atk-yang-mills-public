import MCore.YangMills.A1.PhantomBridgeTriviality

namespace MCore.YangMills.A1

open MeasureTheory

/-!
Y01 hardening layer.

This file does not prove Yang--Mills existence or a mass gap.  It repairs the
specific specification defects certified by PhantomBridgeTriviality:

* reflection positivity is bound to an actual regulated fiber of C;
* the transfer operator acts on an actual regulated fiber of C;
* both interfaces carry explicit non-triviality;
* uniform regulator control cannot be discharged by estimate := 0.

The resulting endpoint is intentionally harder to inhabit.  It is a
fail-closed replacement interface, not a physical existence theorem.
-/

/-- Reflection-positivity data attached to one admissible regulated fiber.
The test space is the actual state space of C at (a,L), so C is no longer a
phantom parameter.  Nontriviality rules out the universal zero-pairing witness. -/
structure BoundReflectionPositivityData (C : RegulatedYM4Construction) where
  a : C.Signature.Regulator
  L : C.Signature.Volume
  admissible : C.admissible a L
  reflect : (C.fiber a L).State → (C.fiber a L).State
  pairing : (C.fiber a L).State → (C.fiber a L).State → ℂ
  involutive : ∀ f, reflect (reflect f) = f
  hermitianReflection :
    ∀ f, pairing (reflect f) f = star (pairing f (reflect f))
  nonnegative : ∀ f, 0 ≤ (pairing (reflect f) f).re
  nontrivial : ∃ f, pairing (reflect f) f ≠ 0

/-- The zero pairing cannot satisfy the hardened reflection boundary. -/
theorem bound_reflection_excludes_zero_pairing
    {C : RegulatedYM4Construction}
    (B : BoundReflectionPositivityData C) :
    ¬ (∀ x y, B.pairing x y = 0) := by
  intro hzero
  rcases B.nontrivial with ⟨f, hf⟩
  exact hf (hzero _ _)

/-- Positive-transfer data attached to one admissible regulated fiber.
The Hilbert structure must be carried by that fiber itself rather than by an
unrelated auxiliary type.  The transfer is explicitly nonzero. -/
structure BoundPositiveTransferData (C : RegulatedYM4Construction) where
  a : C.Signature.Regulator
  L : C.Signature.Volume
  admissible : C.admissible a L
  [instNormedAddCommGroup : NormedAddCommGroup (C.fiber a L).State]
  [instInnerProductSpace : InnerProductSpace ℂ (C.fiber a L).State]
  transfer : (C.fiber a L).State →L[ℂ] (C.fiber a L).State
  positive : ∀ x, 0 ≤ (inner x (transfer x) : ℂ).re
  symmetric : ∀ x y, (inner (transfer x) y : ℂ) = inner x (transfer y)
  contraction : ∀ x, ‖transfer x‖ ≤ ‖x‖
  nonzero : transfer ≠ 0

attribute [instance] BoundPositiveTransferData.instNormedAddCommGroup
attribute [instance] BoundPositiveTransferData.instInnerProductSpace

theorem bound_transfer_excludes_zero_operator
    {C : RegulatedYM4Construction}
    (B : BoundPositiveTransferData C) :
    B.transfer ≠ 0 :=
  B.nonzero

/-- Uniformity strengthened only enough to reject the already-certified
estimate := 0 counterexample.  This still does not identify the estimate with
a physical mass-gap observable; that semantic adapter remains open. -/
structure BoundUniformRegulatorControl (C : RegulatedYM4Construction)
    extends UniformRegulatorControl C where
  nontrivialFinite :
    ∃ a L, C.admissible a L ∧ 0 < estimate a L

theorem bound_uniformity_excludes_zero_estimate
    {C : RegulatedYM4Construction}
    (U : BoundUniformRegulatorControl C) :
    ¬ (∀ a L, U.estimate a L = 0) := by
  intro hzero
  rcases U.nontrivialFinite with ⟨a, L, _, hpos⟩
  rw [hzero a L] at hpos
  exact lt_irrefl 0 hpos

/-- Fail-closed A1 witness after the three certified vacuity attacks. -/
structure HardenedA1ScientificWitness (C : RegulatedYM4Construction) where
  measureInvariance : MeasureInvariance C
  observableInvariance : ObservableInvariance C
  reflectionPositivity : BoundReflectionPositivityData C
  positiveTransfer : BoundPositiveTransferData C
  uniformity : BoundUniformRegulatorControl C

def HardenedA1ScientificOpenBridge (C : RegulatedYM4Construction) : Prop :=
  Nonempty (HardenedA1ScientificWitness C)

/-- A hardened witness still supplies the legacy typed B1/B2 laws, but unlike
the legacy A1 interface there is no generic constructor from B1+B2 alone. -/
theorem hardened_a1_supplies_B1_B2
    {C : RegulatedYM4Construction}
    (W : HardenedA1ScientificWitness C) :
    MeasureInvariance C ∧ ObservableInvariance C :=
  ⟨W.measureInvariance, W.observableInvariance⟩

/-- The three previously-vacuous components now expose concrete
non-triviality consequences that can be used by semantic CI. -/
theorem hardened_a1_nontriviality_packet
    {C : RegulatedYM4Construction}
    (W : HardenedA1ScientificWitness C) :
    (¬ (∀ x y, W.reflectionPositivity.pairing x y = 0)) ∧
    W.positiveTransfer.transfer ≠ 0 ∧
    (¬ (∀ a L, W.uniformity.estimate a L = 0)) := by
  exact ⟨
    bound_reflection_excludes_zero_pairing W.reflectionPositivity,
    W.positiveTransfer.nonzero,
    bound_uniformity_excludes_zero_estimate W.uniformity
  ⟩

#print axioms MCore.YangMills.A1.bound_reflection_excludes_zero_pairing
#print axioms MCore.YangMills.A1.bound_transfer_excludes_zero_operator
#print axioms MCore.YangMills.A1.bound_uniformity_excludes_zero_estimate
#print axioms MCore.YangMills.A1.hardened_a1_supplies_B1_B2
#print axioms MCore.YangMills.A1.hardened_a1_nontriviality_packet

end MCore.YangMills.A1
