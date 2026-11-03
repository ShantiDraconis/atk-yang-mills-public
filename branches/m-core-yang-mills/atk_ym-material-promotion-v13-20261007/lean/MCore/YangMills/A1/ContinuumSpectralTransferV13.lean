import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real
import MCore.YangMills.A1.FiniteRegulatedSpectralV13

namespace MCore.YangMills.A1

open Filter Topology

/--
Sufficient, non-endpoint-equivalent regulator-to-continuum data for V13.

The material content is support preservation below one fixed positive lower
edge, uniformly/eventually in the regulator, together with convergence of the
quadratic-form norm and energy.  No continuum mass-gap inequality is stored.
-/
structure ContinuumSpectralTransferV13 where
  State : Type
  mass : ℝ
  massPositive : 0 < mass
  massBelowFinite : ℕ → State → ℝ → ℝ
  normSqFinite : ℕ → State → ℝ
  energyFinite : ℕ → State → ℝ
  normSqContinuum : State → ℝ
  energyContinuum : State → ℝ

  /-- Strong support preservation: for each state, all sufficiently large
  regulators simultaneously have no spectral mass below the fixed edge. -/
  eventualLowSpectrumExclusion :
    ∀ psi,
      ∀ᶠ n in atTop,
        ∀ r : ℝ, r < mass → massBelowFinite n psi r = 0

  normSq_tendsto :
    ∀ psi,
      Tendsto (fun n => normSqFinite n psi) atTop
        (𝓝 (normSqContinuum psi))

  energy_tendsto :
    ∀ psi,
      Tendsto (fun n => energyFinite n psi) atTop
        (𝓝 (energyContinuum psi))

/--
If the already-certified finite theorem turns low-spectrum exclusion into the
finite quadratic-form bound, then a material continuum transfer witness
preserves that bound in the limit.
-/
theorem continuum_gap_from_eventual_finite_gap_V13
    (B : ContinuumSpectralTransferV13)
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
    tendsto_const_nhds.mul (B.normSq_tendsto psi)
  have hineq :
      ∀ᶠ n in atTop,
        B.mass * B.normSqFinite n psi ≤ B.energyFinite n psi := by
    filter_upwards [B.eventualLowSpectrumExclusion psi] with n hn
    exact hfiniteGap n psi hn
  exact
    le_of_tendsto_of_tendsto
      hnorm
      (B.energy_tendsto psi)
      hineq

#print axioms MCore.YangMills.A1.continuum_gap_from_eventual_finite_gap_V13

end MCore.YangMills.A1
