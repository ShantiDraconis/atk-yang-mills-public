import MCore.YangMills.A1.MaterialHardeningV3

namespace MCore.YangMills.A1

/--
Concrete negative-side regulated gap object on the SAME construction and
transfer operator.

It exhibits admissible regulated models with positive cutoff tending to zero
while the exact B4 spectral gap tends to zero.
-/
structure UniformGapFailureSequence
    (C : RegulatedYM4Construction)
    (P : A1PhysicalData C)
    (B4 : PositiveTransferDataV2 C P) where
  regulator : ℕ → C.Signature.Regulator
  volume : ℕ → C.Signature.Volume

  admissible :
    ∀ n, C.admissible (regulator n) (volume n)

  cutoff_pos :
    ∀ n, 0 < P.cutoffValue (regulator n)

  cutoff_tendsto_zero :
    Filter.Tendsto
      (fun n => P.cutoffValue (regulator n))
      Filter.atTop
      (nhds 0)

  gap_tendsto_zero :
    Filter.Tendsto
      (fun n => B4.spectralGap (regulator n) (volume n))
      Filter.atTop
      (nhds 0)

/--
Any positive uniform mass lower bound on all sufficiently small admissible
cutoffs is incompatible with a same-model gap-failure sequence.
-/
theorem UniformGapFailureSequence.incompatible_with_uniform_mass
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P}
    (F : UniformGapFailureSequence C P B4)
    (U : UniformRegulatorControlV2 C P B3 B4) :
    False := by
  have hcutEventually :
      ∀ᶠ n in Filter.atTop,
        P.cutoffValue (F.regulator n) < U.a0 := by
    have hnhds :
        Set.Iio U.a0 ∈ nhds (0 : ℝ) := by
      exact Iio_mem_nhds U.ha0
    exact F.cutoff_tendsto_zero.eventually hnhds

  have hgapEventually :
      ∀ᶠ n in Filter.atTop,
        B4.spectralGap (F.regulator n) (F.volume n) < U.m0 := by
    have hnhds :
        Set.Iio U.m0 ∈ nhds (0 : ℝ) := by
      exact Iio_mem_nhds U.hm0
    exact F.gap_tendsto_zero.eventually hnhds

  have hboth :
      ∀ᶠ n in Filter.atTop,
        P.cutoffValue (F.regulator n) < U.a0 ∧
        B4.spectralGap (F.regulator n) (F.volume n) < U.m0 :=
    hcutEventually.and hgapEventually

  rcases (Filter.eventually_atTop.1 hboth) with ⟨N, hN⟩
  have hs := hN N (Nat.le_refl N)
  have huniform :=
    U.h_uniform
      (F.regulator N)
      (F.volume N)
      (F.admissible N)
      (F.cutoff_pos N)
      hs.1
  rw [U.h_gap_eq] at huniform
  linarith [hs.2]

/--
Therefore the same regulated transfer system cannot simultaneously carry
a positive UniformRegulatorControlV2 and a concrete vanishing-gap sequence.
-/
theorem no_positive_and_vanishing_gap_same_model
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B3 : ReflectionPositivityDataV2 C P}
    {B4 : PositiveTransferDataV2 C P} :
    (Nonempty (UniformRegulatorControlV2 C P B3 B4)) →
    (Nonempty (UniformGapFailureSequence C P B4)) →
    False := by
  rintro ⟨U⟩ ⟨F⟩
  exact F.incompatible_with_uniform_mass U

/--
Quantitative threshold consequence of a vanishing gap sequence: every positive
mass threshold is violated by some sufficiently late admissible regulator.
-/
theorem UniformGapFailureSequence.below_every_positive_mass
    {C : RegulatedYM4Construction}
    {P : A1PhysicalData C}
    {B4 : PositiveTransferDataV2 C P}
    (F : UniformGapFailureSequence C P B4)
    (m : ℝ)
    (hm : 0 < m) :
    ∃ n,
      B4.spectralGap (F.regulator n) (F.volume n) < m := by
  have hEventually :
      ∀ᶠ n in Filter.atTop,
        B4.spectralGap (F.regulator n) (F.volume n) < m := by
    have hnhds : Set.Iio m ∈ nhds (0 : ℝ) :=
      Iio_mem_nhds hm
    exact F.gap_tendsto_zero.eventually hnhds
  rcases (Filter.eventually_atTop.1 hEventually) with ⟨N, hN⟩
  exact ⟨N, hN N (Nat.le_refl N)⟩

#print axioms MCore.YangMills.A1.UniformGapFailureSequence.incompatible_with_uniform_mass
#print axioms MCore.YangMills.A1.no_positive_and_vanishing_gap_same_model
#print axioms MCore.YangMills.A1.UniformGapFailureSequence.below_every_positive_mass

end MCore.YangMills.A1
