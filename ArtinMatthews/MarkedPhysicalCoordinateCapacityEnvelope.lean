module

public import ArtinMatthews.MarkedPhysicalCoordinateLineTerms
public import ArtinMatthews.MarkedMemoryActualCapacityCorrection
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

/-! The actual omitted-cap correction on each fixed-coordinate row
inherits the proved original small-B envelope, including the true good
volume. The normalized box has mass 15, retained explicitly. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCoordinateCapacityTerm_envelope
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop,∀ (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (d₀ Y Q q U W : ℝ),0≤q → q≤1 → ∀ (B : ℕ) (hB : 1≤B)
      (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) B),
      ‖markedPhysicalCoordinateCapacityTerm e x V ψ η d₀ Y Q i hB q U W (markedDirtyMemoryCutoff x)‖≤
        15*markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x*
          ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖ := by
  filter_upwards [markedMemoryActualCapacityCorrection_envelope e he] with x hx
  intro V ψ η d₀ Y Q q U W hq0 hq1 B hB i
  have hv := markedPhysicalCoordinateIndexGoodVolume_bounds e x d₀ Y U W i hB
  have he0 : 0 ≤ markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x := by
    unfold markedMemoryOrphanTailEnvelope
    positivity
  unfold markedPhysicalCoordinateCapacityTerm markedPhysicalCoordinatePathApply
  split_ifs with ha hc hloop
  · dsimp only
    let d := markedPhysicalCoordinateIndexActivePath (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i hB ha hc
    let c := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
    let v := markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB
    have hvn : ‖(v:ℂ)‖≤15 := by
      simpa only [v,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv.1] using hv.2
    have hh := hx q hq0 hq1 (markedPrimitiveCoordinateTube B)
      (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2)
      d c
    calc
      _ = ‖(v:ℂ)‖*‖markedMemoryPathCapacityCorrection
        (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2) d q (markedDirtyMemoryCutoff x) c‖ :=
        norm_mul _ _
      _ ≤ 15*(markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x*
          ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖) :=
        mul_le_mul hvn hh (norm_nonneg _) (by norm_num : (0:ℝ)≤15)
      _ = _ := by ring
  all_goals rw [norm_zero]; positivity

end
end ArtinMatthews
