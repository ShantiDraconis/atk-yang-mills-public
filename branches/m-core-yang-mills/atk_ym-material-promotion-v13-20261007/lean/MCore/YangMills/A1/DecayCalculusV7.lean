import MCore.YangMills.A1.DerivedAnalyticLawsV6

namespace MCore.YangMills.A1

/-- Continuous decay profile associated with a nonnegative mass scale. -/
noncomputable def decayProfile (m t : ℝ) : ℝ :=
  Real.exp (-t * m)

@[simp] theorem decayProfile_zero_time (m : ℝ) :
    decayProfile m 0 = 1 := by
  simp [decayProfile]

theorem decayProfile_pos (m t : ℝ) :
    0 < decayProfile m t := by
  exact Real.exp_pos _

/-- Exact semigroup law for the exponential decay profile. -/
theorem decayProfile_add_time (m s t : ℝ) :
    decayProfile m (s + t) =
      decayProfile m s * decayProfile m t := by
  unfold decayProfile
  rw [← Real.exp_add]
  congr 1
  ring

/-- Positive mass makes the decay profile antitone in time. -/
theorem decayProfile_antitone
    {m : ℝ} (hm : 0 ≤ m) :
    Antitone (decayProfile m) := by
  intro s t hst
  unfold decayProfile
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Strictly positive mass makes the decay profile strictly decreasing. -/
theorem decayProfile_strictAnti
    {m : ℝ} (hm : 0 < m) :
    StrictAnti (decayProfile m) := by
  intro s t hst
  unfold decayProfile
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- For nonnegative time and mass, the profile lies below one. -/
theorem decayProfile_le_one
    {m t : ℝ}
    (hm : 0 ≤ m)
    (ht : 0 ≤ t) :
    decayProfile m t ≤ 1 := by
  unfold decayProfile
  calc
    Real.exp (-t * m) ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = 1 := Real.exp_zero

/-- Exact first derivative of the continuous decay law. -/
theorem decayProfile_hasDerivAt (m t : ℝ) :
    HasDerivAt (decayProfile m)
      (-m * decayProfile m t) t := by
  unfold decayProfile
  convert
    (Real.hasDerivAt_exp (-t * m)).comp t
      (((hasDerivAt_id t).neg).mul_const m) using 1 <;> ring

/-- For positive mass the derivative is strictly negative everywhere. -/
theorem decayProfile_derivative_neg
    {m t : ℝ}
    (hm : 0 < m) :
    -m * decayProfile m t < 0 := by
  have hneg : -m < 0 := by linarith
  exact mul_neg_of_neg_of_pos hneg (decayProfile_pos m t)

/-- The V3 physical mass inherits the full continuous decay calculus. -/
theorem material_decayProfile_strictAnti
    {C : RegulatedYM4Construction}
    (W : A1MaterialWitnessV3 C) :
    StrictAnti (decayProfile W.uniformMass.m0) :=
  decayProfile_strictAnti W.uniformMass.hm0

theorem material_decayProfile_hasDerivAt
    {C : RegulatedYM4Construction}
    (W : A1MaterialWitnessV3 C)
    (t : ℝ) :
    HasDerivAt (decayProfile W.uniformMass.m0)
      (-W.uniformMass.m0 *
        decayProfile W.uniformMass.m0 t) t :=
  decayProfile_hasDerivAt W.uniformMass.m0 t

#print axioms MCore.YangMills.A1.decayProfile_add_time
#print axioms MCore.YangMills.A1.decayProfile_antitone
#print axioms MCore.YangMills.A1.decayProfile_strictAnti
#print axioms MCore.YangMills.A1.decayProfile_hasDerivAt
#print axioms MCore.YangMills.A1.decayProfile_derivative_neg
#print axioms MCore.YangMills.A1.material_decayProfile_hasDerivAt

end MCore.YangMills.A1
