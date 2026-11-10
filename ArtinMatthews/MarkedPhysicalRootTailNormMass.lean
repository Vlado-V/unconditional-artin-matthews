module

public import ArtinMatthews.MarkedPhysicalRootDiscrepancyMass
public import ArtinMatthews.MarkedPhysicalSelectedAverageTail
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

/-! Absolute root-tail mass is controlled by its actual discrepancy
and the nonnegative averaged tail. No signed cancellation is used. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPhysicalSelectedRootTailNormMass
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) {R : ℕ} (hR : 1 ≤ R) (k : ℕ) : ℝ :=
  markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
      ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
          markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard k,
        ‖markedPhysicalCoordinateSelectedRoot e x
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          ψ η d₀ Y Q i hR q U Vr T‖

theorem markedPhysicalSelectedRootTailNormMass_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) {R : ℕ} (hR : 1 ≤ R) (k : ℕ) :
    markedPhysicalSelectedRootTailNormMass e x ψ η d₀ Y Q q U Vr hR k ≤
      markedPhysicalCoordinateDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr k+
      markedPhysicalSelectedAverageTailMass e x ψ η d₀ Y Q q U Vr hR k := by
  have hm : 0 ≤ markedPhysicalMass
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) :=
    markedPhysicalMass_nonneg _ _ (fun _ => by unfold bandReciprocalMass; positivity)
  unfold markedPhysicalSelectedRootTailNormMass markedPhysicalCoordinateDiscrepancyMass
    markedPhysicalSelectedAverageTailMass
  rw [← mul_add,← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ hm
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T _
  exact norm_le_norm_sub_add _ _

theorem markedPhysicalSelectedRootOddTailNormMass_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U Vr : ℝ) {R : ℕ} (hR : 1 ≤ R)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hUV : 0 ≤ U*Vr) :
    markedPhysicalSelectedRootTailNormMass e x ψ η d₀ Y Q q U Vr hR
        (2*markedPhysicalBonferroniDepth x+1) ≤
      markedPhysicalOddRootDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr+
      (U*Vr/(riemannZeta 2).re)*
        markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y Q q U Vr R hR :=
by
  let k := 2*markedPhysicalBonferroniDepth x+1
  let a := markedPhysicalSelectedRootTailNormMass e x ψ η d₀ Y Q q U Vr hR k
  let b := markedPhysicalCoordinateDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr k
  let c := markedPhysicalSelectedAverageTailMass e x ψ η d₀ Y Q q U Vr hR k
  let d := (U*Vr/(riemannZeta 2).re)*
    markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y Q q U Vr R hR
  have ha : a ≤ b+c := markedPhysicalSelectedRootTailNormMass_le e x ψ η d₀ Y Q q U Vr hR k
  have hc : c ≤ d := markedPhysicalSelectedAverageTailMass_le e x ψ η d₀ Y Q q U Vr hR hq0 hq1 hUV
  change a ≤ b+d
  linarith


end
end ArtinMatthews
