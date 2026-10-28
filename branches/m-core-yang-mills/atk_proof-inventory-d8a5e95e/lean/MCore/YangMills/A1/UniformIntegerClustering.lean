import MCore.PhysicalGapScaling

namespace MCore

/-- Integer-distance exponential clustering induced by the physical transfer
bound, uniformly in cutoff and volume. -/
def UniformIntegerDistanceClustering
    (R : ℝ → ℕ → PhysicalTransferGapData)
    (m0 a0 : ℝ) : Prop :=
  0 < m0 ∧ 0 < a0 ∧
    ∀ (a : ℝ) (L n : ℕ), 0 < a → a < a0 →
      (R a L).cutoff = a ∧
      (R a L).transferNorm ^ n ≤
        Real.exp (-((n : ℝ) * a) * m0)

/-- No new scientific hypothesis is needed for the discrete-distance
propagation: it is a direct consequence of the certified one-step physical
mass lower bound. -/
theorem uniform_physical_mass_lower_bound_implies_integer_clustering
    (R : ℝ → ℕ → PhysicalTransferGapData)
    (m0 a0 : ℝ)
    (h : UniformPhysicalMassLowerBound R m0 a0) :
    UniformIntegerDistanceClustering R m0 a0 := by
  rcases h with ⟨hm0, ha0, hR⟩
  refine ⟨hm0, ha0, ?_⟩
  intro a L n ha ha_lt
  rcases hR a L ha ha_lt with ⟨hcut, hmass⟩
  rcases hmass with ⟨_, hstep⟩
  refine ⟨hcut, ?_⟩
  -- `hstep` is stated with `(R a L).cutoff`; `hcut` identifies it with `a`.
  rw [hcut] at hstep
  exact physical_mass_bound_iterates
    (R a L).transferNorm a m0 n
    (R a L).transferNorm_nonneg hstep

/-- The scientific frontier after this theorem is no longer iteration of a
transfer bound. It is the construction of a uniform physical bound and the
OS/reconstruction step that identifies it with the Hamiltonian mass gap. -/
def Y01PostIntegerClusteringFrontier
    (R : ℝ → ℕ → PhysicalTransferGapData) (m0 a0 : ℝ) : Prop :=
  UniformPhysicalMassLowerBound R m0 a0

#print axioms MCore.uniform_physical_mass_lower_bound_implies_integer_clustering

end MCore
