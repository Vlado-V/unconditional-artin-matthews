module

public import ArtinMatthews.MarkedPhysicalSharpIndexBudget
public import ArtinMatthews.MarkedPhysicalSharpWeightBudget
public import ArtinMatthews.MarkedPhysicalCoordinateIndexCoefficient
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

/-! The complete finite relative-coordinate, ordered-label and copied-
slot coefficient norm sum, multiplied by the original physical mass,
has an explicit .73-power logarithmic cost. Every cardinal and kernel factor
is the literal one on the actual carrier. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def markedPhysicalSharpTotalCost (groups : ℕ) (K Hexp etaBound psiBound Qexp : ℝ) : ℝ :=
  markedPhysicalSharpIndexCost groups K Hexp+
    markedPhysicalSharpWeightCost groups etaBound psiBound Qexp

theorem markedPhysicalSharpTotalCost_nonneg (groups : ℕ) (etaBound : ℝ)
    {K Hexp psiBound Qexp : ℝ} (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp)
    (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp) :
    0 ≤ markedPhysicalSharpTotalCost groups K Hexp etaBound psiBound Qexp :=
  add_nonneg (markedPhysicalSharpIndexCost_nonneg groups hK hHexp)
    (markedPhysicalSharpWeightCost_nonneg groups etaBound hpsi hQexp)

theorem markedPhysicalCoordinateCoefficient_actual_total_sharp
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,0 < e j) (he1 : ∀ j,e j ≤ (1/5:ℝ))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K Hexp etaBound psiBound Qexp : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound)
    (hQexp : 0 ≤ Qexp) (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound) :
    ∀ᶠ x : ℝ in atTop, ∀ (d₀ Y : ℝ),0 ≤ d₀ → 1 ≤ Y →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
        (∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
            (markedPadSlots x) (markedMemoryMomentLength x)
            (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)),
          ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
            (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y ((Real.log x)^Qexp) i‖) ≤
      Real.exp (markedPhysicalSharpTotalCost (Fintype.card J) K Hexp etaBound psiBound Qexp *
        (Real.log x)^(73/100:ℝ)) := by
  filter_upwards [markedPhysicalCoordinateWeight_actual_sharp e he0 etaBound psiBound Qexp hpsi hQexp,
    markedPhysicalActualNormalizer_bounds e he0 etaBound psiBound hpsi,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hw hn hlog
  intro d₀ Y hd₀ hY hscale
  have hL : 0 < Real.log x := by linarith
  have hQ : 1 ≤ (Real.log x)^Qexp := Real.one_le_rpow hlog hQexp
  have hσ := (hn.1 (markedPadSlots x)).1
  have hcoeff := markedPhysicalCoordinateIndexCoefficient_absolute_sum
    (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y ((Real.log x)^Qexp) etaBound psiBound
    hY hQ heta hpsi hη hψ (markedMemoryMomentLength x)
    (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))
  have hcard := markedPhysicalCoordinateIndex_actual_card_sharp e hlog he1 hK
    (mul_nonneg hd₀ (zero_le_one.trans hY)) hHexp hscale
  calc
    _ ≤ markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
        ((Fintype.card (MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) (markedMemoryMomentLength x)
          (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))):ℝ) *
          (markedPhysicalCoordinateEdgeBound (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            etaBound psiBound*((Real.log x)^Qexp)^3)^(markedMemoryMomentLength x)) :=
      mul_le_mul_of_nonneg_left hcoeff hσ
    _ = (Fintype.card (MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) (markedMemoryMomentLength x)
          (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))):ℝ) *
        (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
          (markedPhysicalCoordinateEdgeBound (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            etaBound psiBound*((Real.log x)^Qexp)^3)^(markedMemoryMomentLength x)) := by ring
    _ ≤ Real.exp (markedPhysicalSharpIndexCost (Fintype.card J) K Hexp*(Real.log x)^(73/100:ℝ)) *
        Real.exp (markedPhysicalSharpWeightCost (Fintype.card J) etaBound psiBound Qexp*(Real.log x)^(73/100:ℝ)) :=
      mul_le_mul hcard hw (by unfold markedPhysicalCoordinateEdgeBound; positivity) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      unfold markedPhysicalSharpTotalCost
      ring

end
end ArtinMatthews
