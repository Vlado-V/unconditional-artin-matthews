module

public import ArtinMatthews.MarkedPhysicalCoordinateLineTerms
public import ArtinMatthews.MarkedEstimateActualModel
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

/-! Actual prime-band growth discharges the baseline and disjointness
conditions of the finite independent-line cap split. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalActualCoordinate_baseline_nonzero
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop,∀ (q : ℝ),0≤q → q≤1 →
      ∀ j (p : markedRawActualPrimeBand e x j),markedMemoryBaseline q (markedMemoryMomentLength x) p.1≠0 := by
  filter_upwards [markedMemoryMomentLength_prime_small_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hn hlog
  intro q hq0 hq1 j p
  have hmem : (p.1:ℕ)∈markedLogPowerBand (e j) x := (mem_markedRawPrimeBand _ p.1).mp p.2
  have hlarge := hn _ (marked_band_common_lower (he j) hlog hmem)
  have hb := (markedMemoryBaseline_bounds hq0 hq1 hlarge).1
  linarith

theorem markedPhysicalCoordinateLineTerm_actual_cap_split
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ)
    (he : ∀ j,(1/10:ℝ)≤e j) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop,∀ (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (d₀ Y Q q U W : ℝ),0≤q → q≤1 → ∀ (B : ℕ) (hB : 1≤B)
      (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) B) (cap : ℕ),
      markedPhysicalCoordinateIndependentTerm e x V ψ η d₀ Y Q i hB q U W=
        markedPhysicalCoordinateCappedTerm e x V ψ η d₀ Y Q i hB q U W cap+
        markedPhysicalCoordinateCapacityTerm e x V ψ η d₀ Y Q i hB q U W cap := by
  filter_upwards [markedPhysicalActualCoordinate_baseline_nonzero e he,
    marked_array_disjoint_eventually e hinj] with x hb hd
  intro V ψ η d₀ Y Q q U W hq0 hq1 B hB i cap
  apply markedPhysicalCoordinateLineTerm_cap_split e x V ψ η d₀ Y Q i hB q U W cap
  · intro j k hjk
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.disjoint_left.mp (hd hjk))
      ((mem_markedRawPrimeBand _ _).mp hp) ((mem_markedRawPrimeBand _ _).mp hq)
  · exact hb q hq0 hq1

end
end ArtinMatthews
