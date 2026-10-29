import MCore.YangMills.A1.B6AtomicObligations
import MCore.PhysicalGapScaling

/-!
FAST-GATE refinement of the B6 limit frontier.

This file introduces no Yang--Mills scientific witness.  It replaces the
monolithic search target by explicit data-bearing interfaces whose inhabitants
must be supplied by exact mathematics.  In particular, no RG monotonicity and
no continuum mass gap are assumed or claimed.
-/

namespace MCore.YangMills.A1

/-- Explicit two-regulator family used by the hardening layer. -/
structure B6RegulatedGapFamily where
  Cutoff : Type
  Volume : Type
  Scale : Type
  gap : Cutoff → Volume → Scale
  positive : Scale → Prop
  lowerBound : Scale → Scale → Prop

/-- 7a: pointwise positive gap data.  This is deliberately weaker than
uniformity and is not promoted to the B6 limit block. -/
structure B6GapAtRegulator (R : B6RegulatedGapFamily) where
  gapAt : R.Cutoff → R.Volume → R.Scale
  positiveAt : ∀ a V, R.positive (gapAt a V)
  boundedByPhysicalGap : ∀ a V, R.lowerBound (gapAt a V) (R.gap a V)

/-- 7c: the real uniformity target: one positive scale works for every cutoff
and volume. -/
structure B6UniformLowerBound (R : B6RegulatedGapFamily) where
  delta : R.Scale
  deltaPositive : R.positive delta
  uniform : ∀ a V, R.lowerBound delta (R.gap a V)

/-- UV control is kept separate from IR control.  The predicates are supplied
by a concrete analytic realization rather than hidden in generic Prop fields. -/
structure B6UVControl (R : B6RegulatedGapFamily) where
  LimitObject : Type
  cutoffConverges : R.Cutoff → LimitObject → Prop
  limit : LimitObject
  converges : ∀ a, cutoffConverges a limit
  preservesUniformLowerBound :
    B6UniformLowerBound R → Prop

structure B6IRControl (R : B6RegulatedGapFamily) where
  InfiniteVolumeObject : Type
  volumeConverges : R.Volume → InfiniteVolumeObject → Prop
  limit : InfiniteVolumeObject
  converges : ∀ V, volumeConverges V limit
  preservesUniformLowerBound :
    B6UniformLowerBound R → Prop

/-- Spectral stability is not automatic from an arbitrary weak limit.  The
concrete realization must provide the convergence notion and the preservation
law explicitly. -/
structure B6GapLimitStability (R : B6RegulatedGapFamily) where
  LimitSpectrum : Type
  convergesInSpectralTopology : Prop
  limitGapBound : R.Scale → LimitSpectrum → Prop
  limitSpectrum : LimitSpectrum
  preserves :
    ∀ U : B6UniformLowerBound R,
      convergesInSpectralTopology →
      limitGapBound U.delta limitSpectrum

/-- Exact fast-gate bundle.  Merely constructing pointwise gaps is insufficient;
the uniform lower bound remains an explicit mandatory field. -/
structure B6HardenedLimitCore (R : B6RegulatedGapFamily) where
  pointwise : B6GapAtRegulator R
  uniform : B6UniformLowerBound R
  uv : B6UVControl R
  ir : B6IRControl R
  stability : B6GapLimitStability R
  uvPreserves : uv.preservesUniformLowerBound uniform
  irPreserves : ir.preservesUniformLowerBound uniform
  stableAtLimit : stability.limitGapBound uniform.delta stability.limitSpectrum

/-- Fail-closed fact: pointwise data alone do not construct a uniform witness.
The implication is intentionally absent; callers must provide the uniform
field explicitly. -/
def B6_FIRST_OPEN_TYPE (R : B6RegulatedGapFamily) : Type :=
  B6UniformLowerBound R

def B6_HARDENED_LIMIT_OPEN_MATH : Prop :=
  ∃ R : B6RegulatedGapFamily, Nonempty (B6HardenedLimitCore R)

end MCore.YangMills.A1