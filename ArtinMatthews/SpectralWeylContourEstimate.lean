module

public import ArtinMatthews.SpectralWeylContourIntegrand
public import ArtinMatthews.SpectralWeylContourShift
public import ArtinMatthews.SpectralWeylShiftedLineBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
noncomputable section

theorem spectralWeylContour_integral_bound
    (cylinder : ℂ → ℝ → ℂ) (H base : ℂ → ℂ)
    (hFactor : ∀ z : ℂ, H z = base z*spectralABLCoshCancellation z)
    (hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ B/(1+t^2)^2)
    (hhol : ∀ R X : ℝ, 1 ≤ R → 0 < X → ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 →
      DifferentiableAt ℂ (spectralWeylContourIntegrand cylinder H R X) z) :
    ∃ C : ℝ, 0 < C ∧ ∀ R X : ℝ, 1 ≤ R → 0 < X →
      ‖∫ t : ℝ, spectralWeylContourIntegrand cylinder H R X (t : ℂ)‖ ≤
        C*((X/2)^(5/4 : ℝ)*Real.exp (X^2/4)) := by
  obtain ⟨D,hD,hPoint⟩ := spectralWeylContour_five_eighths_bound cylinder H base
    hFactor hCylinder hB (fun t => hBase t (5/8) (by norm_num) (by norm_num))
  let W := ∫ t : ℝ, SourcePhysical.sourceContourHeightWeight t
  have hW : 0 ≤ W := integral_nonneg (fun t => SourcePhysical.sourceContourHeightWeight_nonneg t)
  refine ⟨D*W+1,by positivity,?_⟩
  intro R X hR hX
  rw [spectralWeylContour_shift cylinder H base hFactor hCylinder hB hBase hR hX (hhol R X hR hX)]
  let P := (X/2)^(5/4 : ℝ)*Real.exp (X^2/4)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hInt := SourcePhysical.sourceContourHeightWeight_integrable.const_mul (D*P)
  calc
    _ ≤ ∫ t : ℝ, (D*P)*SourcePhysical.sourceContourHeightWeight t := by
      apply norm_integral_le_of_norm_le hInt
      exact ae_of_all _ fun t => by
        simpa only [P,SourcePhysical.sourceContourHeightWeight,div_eq_mul_inv] using hPoint R X t hR hX
    _ = D*P*W := by rw [integral_const_mul]
    _ ≤ (D*W+1)*P := by nlinarith

theorem spectralWeylContour_normalized_small_bound
    (cylinder : ℂ → ℝ → ℂ) (H base : ℂ → ℂ)
    (hFactor : ∀ z : ℂ, H z = base z*spectralABLCoshCancellation z)
    (hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ B/(1+t^2)^2)
    (hhol : ∀ R X : ℝ, 1 ≤ R → 0 < X → ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 →
      DifferentiableAt ℂ (spectralWeylContourIntegrand cylinder H R X) z)
    {X₀ : ℝ} (_hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ R X : ℝ, 1 ≤ R → 0 < X → X ≤ X₀ →
      ‖(-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*
        (∫ t : ℝ, spectralWeylContourIntegrand cylinder H R X (t : ℂ))‖ ≤
          C*X^(1/4 : ℝ) := by
  obtain ⟨D,hD,hInt⟩ := spectralWeylContour_integral_bound cylinder H base hFactor
    hCylinder hB hBase hhol
  refine ⟨(4/Real.pi)*D*Real.exp (X₀^2/4),by positivity,?_⟩
  intro R X hR hX hXX
  have hpow : (X/2)^(5/4 : ℝ) ≤ X^(5/4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hexp : Real.exp (X^2/4) ≤ Real.exp (X₀^2/4) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hN : ‖-(4*I)/((Real.pi : ℂ)*(X : ℂ))‖ = (4/Real.pi)/X := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX,
      abs_of_pos Real.pi_pos,div_div]
  have hxp : X^(5/4 : ℝ)/X = X^(1/4 : ℝ) := by
    rw [show (5/4 : ℝ) = 1/4+1 by norm_num,Real.rpow_add hX,Real.rpow_one]
    exact mul_div_cancel_right₀ _ hX.ne'
  rw [norm_mul,hN]
  calc
    _ ≤ ((4/Real.pi)/X)*(D*((X/2)^(5/4 : ℝ)*Real.exp (X^2/4))) := by
      gcongr
      exact hInt R X hR hX
    _ ≤ ((4/Real.pi)/X)*(D*(X^(5/4 : ℝ)*Real.exp (X₀^2/4))) := by gcongr
    _ = ((4/Real.pi)*D*Real.exp (X₀^2/4))*(X^(5/4 : ℝ)/X) := by ring
    _ = _ := by rw [hxp]

end
end ArtinMatthews
