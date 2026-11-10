module

public import ArtinMatthews.MarkedMemoryPathCapacityGeometry
public import ArtinMatthews.MarkedTypeIICollisionDecay
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original baseline-weighted complex capacity correction inherits
the actual small-B scalar envelope uniformly. Its geometric coefficient
is kept literally and its norm is not supplied as a new premise. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem markedMemoryActualCapacityCorrection_envelope
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ),0 ≤ q → q ≤ 1 →
      ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
        (d : MarkedMemoryActivePathData (markedRawActualPrimeBand e x)
          ⌊(Real.log x)^(1/100:ℝ)⌋₊ Z (markedMemoryMomentLength x)) (z : ℂ),
      ‖markedMemoryPathCapacityCorrection hZ d q (markedDirtyMemoryCutoff x) z‖ ≤
        markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x*‖z‖ := by
  filter_upwards [markedMemoryActualCapacityTail_envelope e he,
    markedMemoryMomentLength_prime_small_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x ht hn hlog
  intro q hq0 hq1 Z hZ d z
  have hlarge (j : J) (p : markedRawActualPrimeBand e x j) :
      2*(markedMemoryMomentLength x+1) ≤ (p.1:ℕ)+1 := by
    have hmem : (p.1:ℕ)∈markedLogPowerBand (e j) x :=
      (mem_markedRawPrimeBand _ p.1).mp p.2
    exact hn _ (marked_band_common_lower (he j) hlog hmem)
  exact (markedMemoryPathCapacityCorrection_le hZ d q (markedDirtyMemoryCutoff x) hq0 hq1 hlarge z).trans
    (mul_le_mul_of_nonneg_right (ht q hq0 hq1 Z hZ d).2 (norm_nonneg z))

end
end ArtinMatthews
