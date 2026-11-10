module

public import ArtinMatthews.SpectralABLOppositeKTransform
public import ArtinMatthews.SpectralBareModulusSeries
public import ArtinMatthews.SpectralABLOppositeHeatKernel
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralMixedCuspBesselFibre
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped MatrixGroups Topology ContDiff
noncomputable section

/-- The true-width opposite-sign term with the literal source spatial test. -/
def gamma0ABLOppositeGeometricTerm (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (f : ℝ → ℂ) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
  (gamma0TrueWidthKloostermanSum N r s c.val m n/(C : ℂ))*
    f (4*Real.pi*Real.sqrt (|(m : ℝ)*(n : ℝ)|)/C)

theorem gamma0TrueWidthOppositeBareFibre_eq (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m*n < 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    gamma0TrueWidthBareFibre N r s c m n (spectralABLOppositeFourierWeight f) =
      gamma0ABLOppositeGeometricTerm N r s c m n f/(Real.pi : ℂ) := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let a := |cuspFourierFrequency 1 m|
  let b := |cuspFourierFrequency 1 n|
  let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
  let X := Real.sqrt (a*b)*(2/C)
  let S := gamma0TrueWidthKloostermanSum N r s c.val m n
  have hC : 0 < C := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  have ha : 0 < a := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hb : 0 < b := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hX : 0 < X := by dsimp [X]; positivity
  have hscale : Real.sqrt (a*b)/C^2 = (1/C)*(X/2) := by
    dsimp [X]
    field_simp [hC.ne'] <;> ring
  have harg : X = 4*Real.pi*Real.sqrt (|(m : ℝ)*(n : ℝ)|)/C := by
    simpa only [X,a,b,mul_comm (n : ℝ) (m : ℝ)] using spectral_mixed_weyl_argument C n m
  change S*((Real.sqrt (a*b)/C^2 : ℝ) : ℂ)*
      spectralABLBareKernel (spectralABLOppositeFourierWeight f) m n X =
    ((S/(C : ℂ))*f (4*Real.pi*Real.sqrt (|(m : ℝ)*(n : ℝ)|)/C))/(Real.pi : ℂ)
  calc
    _ = (S/(C : ℂ))*(((X : ℂ)/2)*
        spectralABLBareKernel (spectralABLOppositeFourierWeight f) m n X) := by
      rw [hscale]
      push_cast
      ring
    _ = (S/(C : ℂ))*(f X/(Real.pi : ℂ)) := by
      rw [spectralABLOppositeBareKernel_inverse f hf hc hp hmn hX]
    _ = _ := by rw [harg]; ring

theorem gamma0TrueWidthOppositeHeatSeries_tendsto (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m*n < 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Summable (fun c : Ioi (0 : ℕ) => gamma0ABLOppositeGeometricTerm N r s c m n f) ∧
    Tendsto (fun R : ℝ => ∑' c : Ioi (0 : ℕ),
      gamma0TrueWidthHeatFibre N r s c m n (spectralABLOppositeFourierWeight f) R) atTop
      (𝓝 ((∑' c : Ioi (0 : ℕ), gamma0ABLOppositeGeometricTerm N r s c m n f)/(Real.pi : ℂ))) := by
  obtain ⟨hs,ht⟩ := gamma0TrueWidthHeatSeries_tendsto_bare N r s m n hm hn _
    (spectralABLOppositeFourierWeight_integrable f hf hc hp)
    (spectralABLOppositeHeatKernel_small_bound f hf hc hp m n)
  have he (c : Ioi (0 : ℕ)) := gamma0TrueWidthOppositeBareFibre_eq N r s c m n hm hn hmn f hf hc hp
  refine ⟨(hs.mul_right (Real.pi : ℂ)).congr (fun c => ?_),?_⟩
  · rw [he c,div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  · simp_rw [he,tsum_div_const] at ht
    exact ht

end
end ArtinMatthews
