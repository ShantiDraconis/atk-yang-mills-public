import MCore.YangMills.A1.UniformIntegerClustering
import MCore.K14

namespace MCore

/-- K14 clustering data induced by a physical transfer family below cutoff a0.
The local-observable slot records integer separation. -/
def physicalK14ClusteringData
    (R : ℝ → ℕ → PhysicalTransferGapData)
    (a0 : ℝ) :
    K14UniformExpClusteringData where
  Cutoff := {a : ℝ // 0 < a ∧ a < a0}
  Volume := Nat
  LocalObservable := Nat
  Rate := ℝ
  positive := fun m => 0 < m
  uniformDecayBound := fun m a L n =>
    (R a.1 L).cutoff = a.1 ∧
      (R a.1 L).transferNorm ^ n ≤
        Real.exp (-((n : ℝ) * a.1) * m)

/-- The already-certified physical transfer estimate gives exactly the K14
uniform exponential clustering predicate on the admissible cutoff range. -/
theorem uniform_integer_clustering_to_K14
    (R : ℝ → ℕ → PhysicalTransferGapData)
    (m0 a0 : ℝ)
    (h : UniformIntegerDistanceClustering R m0 a0) :
    K14UniformExpClustering (physicalK14ClusteringData R a0) := by
  rcases h with ⟨hm0, ha0, hcl⟩
  refine ⟨m0, hm0, ?_⟩
  intro a L n
  exact hcl a.1 L n a.2.1 a.2.2

/-- Direct route from the physical one-step bound to the K14 clustering
predicate.  The remaining Y01 work is therefore upstream construction of the
uniform physical bound plus downstream reconstruction/spectral identification. -/
theorem uniform_physical_mass_lower_bound_to_K14_clustering
    (R : ℝ → ℕ → PhysicalTransferGapData)
    (m0 a0 : ℝ)
    (h : UniformPhysicalMassLowerBound R m0 a0) :
    K14UniformExpClustering (physicalK14ClusteringData R a0) :=
  uniform_integer_clustering_to_K14 R m0 a0
    (uniform_physical_mass_lower_bound_implies_integer_clustering R m0 a0 h)

#print axioms MCore.uniform_integer_clustering_to_K14
#print axioms MCore.uniform_physical_mass_lower_bound_to_K14_clustering

end MCore
