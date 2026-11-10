module

public import ArtinMatthews.SpectralAmbientBesselAmplitude
public import ArtinMatthews.SpectralPrimitiveFourierPoincare
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralKLCuspWidthTransform
public import ArtinMatthews.SpectralKLPhysicalDilation
public import ArtinMatthews.SpectralNativeAmbientPrimitive
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original compact cusp-height transform is the literal physical
K-order integral for every complex order, including complementary modes. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem cuspBesselTransform_eq_order_integral (ν : ℂ) {q Y : ℝ}
    (hq : 0 < q) (hY : 0 < Y) (ρ : ℝ → ℝ) (hs : tsupport ρ ⊆ Ioi Y) :
    cuspBesselTransform ν q Y ρ =
      ∫ x in Ioi (0 : ℝ), schlafliBesselK ν x*
        (spectralKLHeightPhysicalTest q ρ x/(x : ℂ)) := by
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => hY.trans (hs hy)
  symm
  calc
    _ = ∫ x in Ioi (0 : ℝ),
        (schlafliBesselK ν (q*(x/q))*spectralKLHeightBaseTest ρ (x/q))/(x : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only [spectralKLHeightPhysicalTest]
      rw [mul_div_cancel₀ x hq.ne']
      ring
    _ = ∫ y in Ioi (0 : ℝ), (schlafliBesselK ν (q*y)*spectralKLHeightBaseTest ρ y)/(y : ℂ) :=
      spectralKLPhysical_dilation_integral (fun y : ℝ => schlafliBesselK ν (q*y)*spectralKLHeightBaseTest ρ y) hq
    _ = ∫ y in Ioi (0 : ℝ), cuspBesselTransformIntegrand ν q ρ y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      dsimp only [spectralKLHeightBaseTest,cuspBesselTransformIntegrand,cuspBesselKernel]
      push_cast
      ring
    _ = ∫ y : ℝ, cuspBesselTransformIntegrand ν q ρ y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hρ0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hpρ h))
      simp [cuspBesselTransformIntegrand,hρ0]
    _ = cuspBesselTransform ν q Y ρ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hρ0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
      simp [cuspBesselTransformIntegrand,hρ0]

theorem gamma0PrimitiveFourierPoincareTest_ambient_order_integral (N : ℕ) [NeZero N]
    (eig : ℝ) (heig : 0 ≤ eig) (v : Gamma0RegionL2 N)
    (hG : gamma0Green N v = (((eig+1)⁻¹ : ℝ) : ℂ) • v)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r n ρ hρ hcρ hpρ) v =
      (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)*
        gamma0AmbientBesselAmplitude N eig heig v hG r
          ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn)*
        (∫ x in Ioi (0 : ℝ), schlafliBesselK (Complex.sqrt (1/4-(eig : ℂ))) x*
          (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
            (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)) x/(x : ℂ))) := by
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hq : 0 < |cuspFourierFrequency 1 n| := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hs := (spectral_cusp_width_test_properties _ Y hw ρ hρ.continuous hcρ hsρ).2.2
  rw [gamma0PrimitiveFourierPoincareTest_ambient_inner N eig heig v hG r n hn Y hY ρ hρ hcρ hpρ hsρ,
    cuspBesselTransform_eq_order_integral _ hq (div_pos hY hw) _ hs]

end ArtinMatthews
