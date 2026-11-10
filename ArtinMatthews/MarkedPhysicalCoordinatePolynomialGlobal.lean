module

public import ArtinMatthews.MarkedPhysicalCoordinatePolynomialTerms
public import ArtinMatthews.MarkedPhysicalCoordinateLineGlobal
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

/-! Global performed Bonferroni replacement on the literal independent-
line main term. The full finite coefficient mass and normalized good
volumes are retained, and their source bounds discharge the error. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

def markedPhysicalCoordinatePolynomialGlobal {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U W : ℝ) (B : ℕ) (hB : 1 ≤ B) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x):ℂ)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) B,
      markedPhysicalCoordinatePolynomialTerm e x
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q i hB q U W
        (2*markedPhysicalBonferroniDepth x)

theorem markedPhysicalCoordinatePolynomialGlobal_error_le_tail
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U W : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (B : ℕ) (hB : 1 ≤ B) :
    ‖markedPhysicalCoordinateIndependentGlobal e x ψ η d₀ Y Q q U W B hB-
      markedPhysicalCoordinatePolynomialGlobal e x ψ η d₀ Y Q q U W B hB‖ ≤ 
      markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y Q q U W B hB := by
  let V := fun j => bandReciprocalMass (markedLogPowerBand (e j) x)
  have hv : ∀ j,0 ≤ V j := by intro j; unfold V bandReciprocalMass; positivity
  have hm : 0 ≤ markedPhysicalMass V (markedPadSlots x) := markedPhysicalMass_nonneg V _ hv
  unfold markedPhysicalCoordinateIndependentGlobal markedPhysicalCoordinatePolynomialGlobal
    markedPhysicalCoordinateBonferroniTailMass
  rw [← mul_sub,← Finset.sum_sub_distrib,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hm).trans
  apply mul_le_mul_of_nonneg_left _ hm
  exact Finset.sum_le_sum (fun i _ =>
    markedPhysicalCoordinatePolynomialTerm_error e x V ψ η d₀ Y Q i hB q U W hq0 hq1)

theorem markedPhysicalCoordinatePolynomialGlobal_moment_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,0<e j) (he1 : ∀ j,e j ≤ (1/5:ℝ)) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K Hexp etaBound psiBound Qexp G : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound)
    (hQexp : 0 ≤ Qexp) (hG : 0 ≤ G) (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0 ≤ d₀) (hY : 1 ≤ Y),
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) → ∀ (q U W : ℝ),0 ≤ q → q ≤ 1 →
      let B := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
      let hB := markedPhysicalMomentTubeRadius_ge_one (markedMemoryMomentLength x) hK
        (mul_nonneg hd₀ (zero_le_one.trans hY))
      ‖markedPhysicalCoordinateIndependentGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U W B hB-
        markedPhysicalCoordinatePolynomialGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U W B hB‖ ≤ 
          (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  filter_upwards [markedPhysicalCoordinateBonferroniTailMass_moment_log_saving e he0 he1 hinj
    ψ η K Hexp etaBound psiBound Qexp G hK hHexp heta hpsi hQexp hG hη hψ] with x hx
  intro d₀ Y hd₀ hY hscale q U W hq0 hq1
  exact (markedPhysicalCoordinatePolynomialGlobal_error_le_tail e x ψ η d₀ Y ((Real.log x)^Qexp)
    q U W hq0 hq1 _ _).trans (hx d₀ Y hd₀ hY hscale q U W hq0 hq1)

end
end ArtinMatthews
