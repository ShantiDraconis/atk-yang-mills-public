import MCore.YangMills.A1.K14HamiltonianConcreteRealizationV13
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace MCore.YangMills.A1

open scoped ComplexConjugate

/--
Finite-dimensional regulated realization.  This is the part of the V13
spectral layer that Mathlib currently supports constructively via
self-adjoint diagonalization.
-/
structure FiniteRegulatedHamiltonianV13
    (HSpace : Type)
    [NormedAddCommGroup HSpace]
    [InnerProductSpace ℂ HSpace]
    [CompleteSpace HSpace]
    [FiniteDimensional ℂ HSpace] extends
    K14HamiltonianConcreteRealizationV13 HSpace where

namespace FiniteRegulatedHamiltonianV13

variable
  {HSpace : Type}
  [NormedAddCommGroup HSpace]
  [InnerProductSpace ℂ HSpace]
  [CompleteSpace HSpace]
  [FiniteDimensional ℂ HSpace]

variable (C : FiniteRegulatedHamiltonianV13 HSpace)

/-- The underlying linear map used by the finite-dimensional spectral theorem. -/
def linearHamiltonian : HSpace →ₗ[ℂ] HSpace :=
  C.toK14HamiltonianConcreteRealizationV13.H_op.toLinearMap

theorem linearHamiltonian_isSymmetric :
    C.linearHamiltonian.IsSymmetric := by
  exact
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      C.toK14HamiltonianConcreteRealizationV13.selfAdjoint_concrete)

/--
An orthonormal eigenbasis exists in the finite-dimensional regulated model.
The dimension index is chosen from the actual module finrank.
-/
def eigenbasis :
    OrthonormalBasis
      (Fin (Module.finrank ℂ HSpace)) ℂ HSpace :=
  (C.linearHamiltonian_isSymmetric).eigenvectorBasis rfl

/-- Real eigenvalues associated with the eigenbasis. -/
def eigenvalue (i : Fin (Module.finrank ℂ HSpace)) : ℝ :=
  (C.linearHamiltonian_isSymmetric).eigenvalues rfl i

theorem apply_eigenbasis
    (i : Fin (Module.finrank ℂ HSpace)) :
    C.linearHamiltonian (C.eigenbasis i) =
      (C.eigenvalue i : ℂ) • C.eigenbasis i := by
  simpa [eigenbasis, eigenvalue, linearHamiltonian] using
    (C.linearHamiltonian_isSymmetric).apply_eigenvectorBasis rfl i

/--
Discrete spectral weight of a state at the i-th eigenvalue.
-/
def spectralWeight
    (psi : HSpace)
    (i : Fin (Module.finrank ℂ HSpace)) : ℝ :=
  ‖(C.eigenbasis.repr psi) i‖ ^ 2

theorem spectralWeight_nonneg
    (psi : HSpace)
    (i : Fin (Module.finrank ℂ HSpace)) :
    0 ≤ C.spectralWeight psi i := by
  exact sq_nonneg _

/--
Finite low-energy spectral mass.  This is deliberately a finite sum rather than
an abstract Measure: it is the regulator-level object supported by the
available Mathlib spectral theorem.
-/
def massBelowFinite
    (psi : HSpace)
    (r : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℂ HSpace),
    if C.eigenvalue i ≤ r then C.spectralWeight psi i else 0

theorem massBelowFinite_nonneg
    (psi : HSpace)
    (r : ℝ) :
    0 ≤ C.massBelowFinite psi r := by
  unfold massBelowFinite
  exact Finset.sum_nonneg (fun i hi => by
    by_cases h : C.eigenvalue i ≤ r
    · simp [h, C.spectralWeight_nonneg psi i]
    · simp [h])


/-- Finite Parseval identity for the spectral weights. -/
theorem spectralWeight_sum
    (psi : HSpace) :
    ∑ i : Fin (Module.finrank ℂ HSpace), C.spectralWeight psi i =
      ‖psi‖ ^ 2 := by
  simpa [spectralWeight, OrthonormalBasis.repr_apply_apply] using
    (OrthonormalBasis.sum_sq_norm_inner C.eigenbasis psi)


/-- Finite spectral expectation identity. -/
theorem spectralWeight_expectation
    (psi : HSpace) :
    ∑ i : Fin (Module.finrank ℂ HSpace),
        C.eigenvalue i * C.spectralWeight psi i =
      Complex.re (inner psi (C.linearHamiltonian psi)) := by
  rw [← C.eigenbasis.repr.inner_map_map psi (C.linearHamiltonian psi)]
  rw [PiLp.inner_apply]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hdiag :
      C.eigenbasis.repr (C.linearHamiltonian psi) i =
        (C.eigenvalue i : ℂ) * (C.eigenbasis.repr psi) i := by
    simpa [eigenbasis, eigenvalue, linearHamiltonian] using
      (C.linearHamiltonian_isSymmetric).eigenvectorBasis_apply_self_apply rfl psi i
  rw [hdiag]
  simp [spectralWeight, inner_smul_right, RCLike.inner_apply]
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, pow_two]
  ring


/-- Vanishing of low spectral mass forces every strictly sub-gap weight to vanish. -/
theorem spectralWeight_eq_zero_of_eigenvalue_lt
    {m : ℝ}
    (psi : HSpace)
    (hvan : ∀ r : ℝ, r < m → C.massBelowFinite psi r = 0)
    (i : Fin (Module.finrank ℂ HSpace))
    (hi : C.eigenvalue i < m) :
    C.spectralWeight psi i = 0 := by
  have hsum := hvan (C.eigenvalue i) hi
  unfold massBelowFinite at hsum
  have hterms :
      ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℂ HSpace))),
        (if C.eigenvalue j ≤ C.eigenvalue i then C.spectralWeight psi j else 0) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum
    intro j hj
    by_cases hji : C.eigenvalue j ≤ C.eigenvalue i
    · simp [hji, C.spectralWeight_nonneg psi j]
    · simp [hji]
  have hi0 := hterms i (Finset.mem_univ i)
  simpa only [if_pos le_rfl] using hi0

/--
If every eigenmode carrying nonzero spectral weight lies at or above m, then
the finite low-energy spectral mass vanishes below m.
-/
theorem massBelowFinite_eq_zero_of_weight_support_ge
    {m r : ℝ}
    (psi : HSpace)
    (hr : r < m)
    (hsupport :
      ∀ i : Fin (Module.finrank ℂ HSpace),
        C.spectralWeight psi i ≠ 0 →
        m ≤ C.eigenvalue i) :
    C.massBelowFinite psi r = 0 := by
  unfold massBelowFinite
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hir : C.eigenvalue i ≤ r
  · have hlt : C.eigenvalue i < m := lt_of_le_of_lt hir hr
    have hw : C.spectralWeight psi i = 0 := by
      by_contra hnz
      exact (not_lt_of_ge (hsupport i hnz)) hlt
    simp [hir, hw]
  · simp [hir]

/-- The regulated finite-dimensional mass gap follows from low-spectrum vanishing. -/
theorem finite_mass_gap_of_vanishing_below
    {m : ℝ}
    (psi : HSpace)
    (hvan : ∀ r : ℝ, r < m → C.massBelowFinite psi r = 0) :
    m * ‖psi‖ ^ 2 ≤
      Complex.re (inner psi (C.linearHamiltonian psi)) := by
  calc
    m * ‖psi‖ ^ 2 =
        ∑ i : Fin (Module.finrank ℂ HSpace),
          m * C.spectralWeight psi i := by
      rw [← C.spectralWeight_sum psi, Finset.mul_sum]
    _ ≤ ∑ i : Fin (Module.finrank ℂ HSpace),
          C.eigenvalue i * C.spectralWeight psi i := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hlt : C.eigenvalue i < m
      · rw [C.spectralWeight_eq_zero_of_eigenvalue_lt psi hvan i hlt]
        simp
      · exact
          mul_le_mul_of_nonneg_right
            (le_of_not_gt hlt)
            (C.spectralWeight_nonneg psi i)
    _ = Complex.re (inner psi (C.linearHamiltonian psi)) :=
      C.spectralWeight_expectation psi


/--
A statewise lower spectral-edge bound implies the exact vanishing premise used
by the finite mass-gap theorem.
-/
theorem finite_mass_gap_of_weight_support_ge
    {m : ℝ}
    (psi : HSpace)
    (hsupport :
      ∀ i : Fin (Module.finrank ℂ HSpace),
        C.spectralWeight psi i ≠ 0 →
        m ≤ C.eigenvalue i) :
    m * ‖psi‖ ^ 2 ≤
      Complex.re (inner psi (C.linearHamiltonian psi)) := by
  apply C.finite_mass_gap_of_vanishing_below psi
  intro r hr
  exact C.massBelowFinite_eq_zero_of_weight_support_ge psi hr hsupport


#print axioms MCore.YangMills.A1.FiniteRegulatedHamiltonianV13.linearHamiltonian_isSymmetric
#print axioms MCore.YangMills.A1.FiniteRegulatedHamiltonianV13.apply_eigenbasis
#print axioms MCore.YangMills.A1.FiniteRegulatedHamiltonianV13.spectralWeight_nonneg
#print axioms MCore.YangMills.A1.FiniteRegulatedHamiltonianV13.massBelowFinite_nonneg

end FiniteRegulatedHamiltonianV13

end MCore.YangMills.A1
