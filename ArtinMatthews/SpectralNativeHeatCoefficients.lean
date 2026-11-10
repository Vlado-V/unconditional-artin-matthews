module

public import ArtinMatthews.SpectralNativeHeatProfile
public import ArtinMatthews.SpectralABLWhittakerUniqueness
public import ArtinMatthews.SpectralNativeDecayingContinuous
public import ArtinMatthews.SpectralNativePhysicalTransform
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The Gaussian native tests have literal discrete and continuous
coefficients, including the source rho normalization. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0AmbientABLSourceRho_cuspidal (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N)
    (hG : gamma0Green N (gamma0FullCuspidalSpectralBasis N i).val =
      (((gamma0AllHeightGradientSpectralValue N i+1)⁻¹ : ℝ) : ℂ) •
        (gamma0FullCuspidalSpectralBasis N i).val)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    gamma0AmbientABLSourceRho N (gamma0AllHeightGradientSpectralValue N i)
      (gamma0AllHeightGradientSpectralValue_nonneg N i)
      (gamma0FullCuspidalSpectralBasis N i).val hG r n hn = gamma0ABLSourceRho N i r Y hY n hn := by
  apply gamma0ABLSourceRho_unique N i r Y hY n hn
  exact gamma0AmbientABLSourceRho_fourier_ae N (gamma0AllHeightGradientSpectralValue N i)
    (gamma0AllHeightGradientSpectralValue_nonneg N i) (gamma0FullCuspidalSpectralBasis N i).val hG
    r n hn Y hY

theorem gamma0HeatPoincareTest_ambient_source_coefficient (N : ℕ) [NeZero N]
    (eig : ℝ) (heig : 0 ≤ eig) (v : Gamma0RegionL2 N)
    (hG : gamma0Green N v = (((eig+1)⁻¹ : ℝ) : ℂ) • v)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) :
    inner ℂ (gamma0HeatPoincareTest N r n hn R hR) v =
      (2*Real.sqrt |(n : ℝ)| : ℂ)*gamma0AmbientABLSourceRho N eig heig v hG r n hn*
        Complex.exp ((1/4-(eig : ℂ))/(R : ℂ)^2) := by
  rw [gamma0HeatPoincareTest_ambient_coefficient,gamma0AmbientABLSourceRho,
    spectralABLRhoFromNative_scale _ _ (abs_pos.mpr (by exact_mod_cast hn))]

theorem gamma0HeatPoincareTest_cuspidal_coefficient (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R) :
    inner ℂ (gamma0HeatPoincareTest N r n hn R hR) (gamma0FullCuspidalSpectralBasis N i).val =
      (2*Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLSourceRho N i r Y hY n hn*
        Complex.exp ((1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))/(R : ℂ)^2) := by
  have hG : gamma0Green N (gamma0FullCuspidalSpectralBasis N i).val =
      (((gamma0AllHeightGradientSpectralValue N i+1)⁻¹ : ℝ) : ℂ) •
        (gamma0FullCuspidalSpectralBasis N i).val := by
    simpa only [gamma0AllHeightGradientSpectralValue,sub_add_cancel,inv_inv,
      gamma0AllHeightSpectralValue_real] using gamma0FullCuspidalSpectralBasis_eigen N i
  have h := gamma0HeatPoincareTest_ambient_source_coefficient N (gamma0AllHeightGradientSpectralValue N i)
    (gamma0AllHeightGradientSpectralValue_nonneg N i) (gamma0FullCuspidalSpectralBasis N i).val hG
    r n hn R hR
  rwa [gamma0AmbientABLSourceRho_cuspidal N i hG r Y hY n hn] at h

theorem gamma0HeatPoincareTest_continuous_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (R : ℝ) (hR : 0 < R)
    (Z : ℝ) (hZ : 0 < Z) (i : Gamma0EisensteinCuspClasses N) :
    (gamma0EisensteinAnalysis N (gamma0HeatPoincareTest N r n hn R hR)) i
      =ᵐ[gamma0EisensteinSpectralMeasure] fun t => star
        (gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N i) r Z hZ n hn
          (eisensteinCriticalPoint t)*Complex.exp (-((t : ℂ)^2)/(R : ℂ)^2)) := by
  let P := gamma0HeatHeightProfile N r n hn R hR
  filter_upwards [gamma0PrimitiveDecayingPoincare_continuous_ae N r n hn Z hZ P i] with t ht
  have hk := gamma0NativeOrderTransform_eq_compactOrder N r n hn P.value ((t : ℂ)*Complex.I)
  change gamma0NativeOrderTransform N r n P.value ((t : ℂ)*Complex.I) =
    spectralKLCompactOrderTransform (gamma0PrimitivePhysicalTest N r n P.value) ((t : ℂ)*Complex.I) at hk
  rw [show gamma0PrimitivePhysicalTest N r n P.value = spectralKLHeatProfile R from
    gamma0HeatHeightProfile_physical N r n hn R hR,
    spectralKLHeatProfile_continued_transform R hR _ (by simp)] at hk
  have hsq : ((t : ℂ)*Complex.I)^2 = -((t : ℂ)^2) := by rw [mul_pow,Complex.I_sq]; ring
  rw [hsq] at hk
  change (gamma0EisensteinAnalysis N (gamma0PrimitiveDecayingPoincare N r n P)) i t = _
  rw [ht]
  exact congrArg (fun z : ℂ => star
    (gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N i) r Z hZ n hn
      (eisensteinCriticalPoint t)*z)) hk

end ArtinMatthews
