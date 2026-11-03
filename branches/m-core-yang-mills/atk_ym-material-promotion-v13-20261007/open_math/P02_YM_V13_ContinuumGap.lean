import Mathlib
import MCore.YangMills.A1.FiniteRegulatedSpectralV13

namespace MCore.YangMills.A1

open Filter Topology

/--
P02-YM V13 terminal continuum frontier.

This file contains no endpoint-equivalent axiom and no `sorry`.
The former pointwise low-spectrum limit was too weak: pointwise convergence
cannot transport an exact zero backwards to finite regulators.  The terminal
producer therefore records exactly the missing uniform/eventual exclusion.
-/
structure ContinuumGapBridgeV13 where
  State : Type
  mass : ℝ
  massPositive : 0 < mass
  massBelowFinite : ℕ → State → ℝ → ℝ
  normSqFinite : ℕ → State → ℝ
  energyFinite : ℕ → State → ℝ
  normSqContinuum : State → ℝ
  energyContinuum : State → ℝ

/--
Exact material producer remaining at the continuum frontier.

It does not contain the continuum mass-gap conclusion.  Its nontrivial content
is the eventual uniform preservation of the finite low-spectrum exclusion,
plus convergence of the quadratic-form norm and energy.
-/
structure ContinuumLimitProducerV13 (B : ContinuumGapBridgeV13) where
  eventualLowSpectrumExclusion :
    ∀ psi,
      ∀ᶠ n in atTop,
        ∀ r : ℝ, r < B.mass → B.massBelowFinite n psi r = 0
  normSq_tendsto :
    ∀ psi,
      Tendsto (fun n => B.normSqFinite n psi) atTop
        (𝓝 (B.normSqContinuum psi))
  energy_tendsto :
    ∀ psi,
      Tendsto (fun n => B.energyFinite n psi) atTop
        (𝓝 (B.energyContinuum psi))

/--
Terminal consumer: once the material continuum producer exists, the finite
gap passes to the continuum with no further open mathematics.
-/
theorem continuum_mass_gap_of_finite_limits_V13
    (B : ContinuumGapBridgeV13)
    (P : ContinuumLimitProducerV13 B)
    (hfiniteGap :
      ∀ n psi,
        (∀ r : ℝ, r < B.mass → B.massBelowFinite n psi r = 0) →
        B.mass * B.normSqFinite n psi ≤ B.energyFinite n psi) :
    ∀ psi,
      B.mass * B.normSqContinuum psi ≤ B.energyContinuum psi := by
  intro psi
  have hnorm :
      Tendsto
        (fun n => B.mass * B.normSqFinite n psi)
        atTop
        (𝓝 (B.mass * B.normSqContinuum psi)) :=
    tendsto_const_nhds.mul (P.normSq_tendsto psi)
  have hineq :
      ∀ᶠ n in atTop,
        B.mass * B.normSqFinite n psi ≤ B.energyFinite n psi := by
    filter_upwards [P.eventualLowSpectrumExclusion psi] with n hn
    exact hfiniteGap n psi hn
  exact
    le_of_tendsto_of_tendsto
      hnorm
      (P.energy_tendsto psi)
      hineq

/-- Positivity is carried by the same material bridge, not inferred afterward. -/
theorem continuum_bridge_mass_positive
    (B : ContinuumGapBridgeV13) :
    0 < B.mass :=
  B.massPositive

#print axioms MCore.YangMills.A1.continuum_mass_gap_of_finite_limits_V13
#print axioms MCore.YangMills.A1.continuum_bridge_mass_positive

end MCore.YangMills.A1
