module

public import ArtinMatthews.MarkedPhysicalCoordinateBonferroniTail
public import ArtinMatthews.MarkedPhysicalBandLineBonferroni
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

/-! The literal independent-line coordinate term is compared with its
performed Bonferroni polynomial, retaining the actual support, volume,
and complex coefficient. The error is the genuine selected-modulus tail. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedComplex_weighted_real_difference (c : ℂ) (w a b : ℝ) (hw : 0 ≤ w) :
    ‖(w:ℂ)*((a:ℂ)*c)-(w:ℂ)*((b:ℂ)*c)‖=‖c‖*w*|a-b| := by
  rw [← mul_sub,← sub_mul,← Complex.ofReal_sub,norm_mul,norm_mul,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hw]
  ring

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q : ℝ) {B : ℕ}
  (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
    (markedPadSlots x) (markedMemoryMomentLength x) B) (hB : 1 ≤ B)

def markedPhysicalCoordinatePolynomialTerm (q U W : ℝ) (k : ℕ) : ℂ :=
  markedPhysicalCoordinatePathApply e x V ψ η d₀ Y Q i hB (fun _ c =>
    (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB:ℂ)*
      ((markedPhysicalIndependentBonferroni (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        i.1 q (markedPhysicalCoordinateIndexPath i.2.1)
        (markedPhysicalCoordinateIndexPath_primitive hB i.2.1) k:ℂ)*c))

theorem markedPhysicalCoordinateIndex_expectation_eq (q : ℝ)
    (ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v))
    (hc : markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i≠0) :
    markedMemoryPathIndependentExpectation
      (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2)
      (markedPhysicalCoordinateIndexActivePath (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i hB ha hc) q=
    markedMemoryIndependentLineExpectation
      (markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (markedLogPowerBand (e j) x)))
      (markedPhysicalMarkingPathRawSlots (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i.1) q
      (markedPhysicalCoordinateIndexPath i.2.1) (markedPhysicalCoordinateIndexPath_primitive hB i.2.1) := rfl

theorem markedPhysicalCoordinatePolynomialTerm_error (q U W : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖markedPhysicalCoordinateIndependentTerm e x V ψ η d₀ Y Q i hB q U W-
      markedPhysicalCoordinatePolynomialTerm e x V ψ η d₀ Y Q i hB q U W
        (2*markedPhysicalBonferroniDepth x)‖ ≤ 
      ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖*
      markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB*
      markedPhysicalCoordinateIndexTailMean e x q i hB := by
  have hv := (markedPhysicalCoordinateIndexGoodVolume_bounds e x d₀ Y U W i hB).1
  have ht0 := markedPhysicalCoordinateIndexTailMean_nonneg e x q hq0 hq1 i hB
  unfold markedPhysicalCoordinateIndependentTerm markedPhysicalCoordinatePolynomialTerm
    markedPhysicalCoordinatePathApply
  split_ifs with ha hc hloop
  · dsimp only
    let d := markedPhysicalCoordinateIndexActivePath (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i hB ha hc
    have he := markedPhysicalIndependentBonferroni_error
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i.1 hq0 hq1
      (markedPhysicalCoordinateIndexPath i.2.1) (markedPhysicalCoordinateIndexPath_primitive hB i.2.1)
      (markedPhysicalBonferroniDepth x)
    rw [← markedPhysicalCoordinateIndex_expectation_eq e x V ψ η d₀ Y Q i hB q ha hc] at he
    have he' : |markedMemoryPathIndependentExpectation
        (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2) d q-
        markedPhysicalIndependentBonferroni (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
          i.1 q (markedPhysicalCoordinateIndexPath i.2.1) (markedPhysicalCoordinateIndexPath_primitive hB i.2.1)
          (2*markedPhysicalBonferroniDepth x)| ≤ markedPhysicalCoordinateIndexTailMean e x q i hB := he
    exact (markedComplex_weighted_real_difference _ _ _ _ hv).le.trans
      (mul_le_mul_of_nonneg_left he' (mul_nonneg (norm_nonneg _) hv))
  all_goals simp only [sub_self,norm_zero]; positivity

end
end ArtinMatthews
