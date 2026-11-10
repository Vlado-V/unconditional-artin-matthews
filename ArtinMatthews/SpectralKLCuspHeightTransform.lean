module

public import ArtinMatthews.SpectralKLHeightPhysicalTest
public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralKLAnalysisIntegral
public import ArtinMatthews.SpectralKLAnalysisCalibration
public import ArtinMatthews.SpectralKLCompactInverse
public import ArtinMatthews.SpectralKLPhysicalDilation
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

/-! The existing actual cusp-height Bessel transform is the proved KL
analysis of its literal physical frequency-dilated test. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

theorem cuspBesselTransform_imaginary_eq_KL {q Y : ℝ} (hq : 0 < q) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (hs : tsupport ρ ⊆ Ioi Y) (t : ℝ) :
    cuspBesselTransform ((t : ℂ)*Complex.I) q Y ρ =
      spectralKLPhysicalAnalysisIntegral (spectralKLHeightPhysicalTest q ρ) t := by
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => hY.trans (hs hy)
  have hH := spectralKLHeightPhysicalTest_properties hq ρ hρ hcρ hpρ
  rw [spectralKLPhysicalAnalysisIntegral_eq _ hH.2.2]
  symm
  calc
    _ = ∫ x in Ioi (0 : ℝ),
        (schlafliBesselK ((t : ℂ)*Complex.I) (q*(x/q))*spectralKLHeightBaseTest ρ (x/q))/(x : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only [spectralKLHeightPhysicalTest]
      rw [mul_div_cancel₀ x hq.ne']
    _ = ∫ y in Ioi (0 : ℝ),
        (schlafliBesselK ((t : ℂ)*Complex.I) (q*y)*spectralKLHeightBaseTest ρ y)/(y : ℂ) :=
      spectralKLPhysical_dilation_integral
        (fun y : ℝ => schlafliBesselK ((t : ℂ)*Complex.I) (q*y)*spectralKLHeightBaseTest ρ y) hq
    _ = ∫ y in Ioi (0 : ℝ), cuspBesselTransformIntegrand ((t : ℂ)*Complex.I) q ρ y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      dsimp only [spectralKLHeightBaseTest,cuspBesselTransformIntegrand,cuspBesselKernel]
      push_cast
      ring
    _ = ∫ y : ℝ, cuspBesselTransformIntegrand ((t : ℂ)*Complex.I) q ρ y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hρ0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hpρ h))
      simp [cuspBesselTransformIntegrand,hρ0]
    _ = cuspBesselTransform ((t : ℂ)*Complex.I) q Y ρ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hρ0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
      simp [cuspBesselTransformIntegrand,hρ0]

theorem cuspBesselTransform_imaginary_memLp {q Y : ℝ} (hq : 0 < q) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (hs : tsupport ρ ⊆ Ioi Y) :
    MemLp (fun t : ℝ => cuspBesselTransform ((t : ℂ)*Complex.I) q Y ρ) 2 spectralKLSpectralMeasure := by
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => hY.trans (hs hy)
  obtain ⟨hH,hHc,hHp⟩ := spectralKLHeightPhysicalTest_properties hq ρ hρ hcρ hpρ
  apply (spectralKLPhysicalAnalysisIntegral_memLp _ hH hHc hHp).ae_eq
  exact Filter.Eventually.of_forall (fun t => (cuspBesselTransform_imaginary_eq_KL hq hY ρ hρ hcρ hs t).symm)

theorem cuspBesselTransform_imaginary_plancherel {q Y : ℝ} (hq : 0 < q) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (hs : tsupport ρ ⊆ Ioi Y) :
    (∫ t in Ioi (0 : ℝ), spectralKLPlancherelWeight t*
      ‖cuspBesselTransform ((t : ℂ)*Complex.I) q Y ρ‖^2) =
      ∫ y in Ioi (0 : ℝ), (ρ y)^2/y^2 := by
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => hY.trans (hs hy)
  obtain ⟨hH,hHc,hHp⟩ := spectralKLHeightPhysicalTest_properties hq ρ hρ hcρ hpρ
  calc
    _ = ∫ t in Ioi (0 : ℝ), spectralKLPlancherelWeight t*
        ‖spectralKLPhysicalAnalysisIntegral (spectralKLHeightPhysicalTest q ρ) t‖^2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [cuspBesselTransform_imaginary_eq_KL hq hY ρ hρ hcρ hs t]
    _ = ∫ x in Ioi (0 : ℝ), ‖spectralKLHeightPhysicalTest q ρ x‖^2/x :=
      spectralKLAnalysis_compact_plancherel _ hH hHc hHp
    _ = ∫ y in Ioi (0 : ℝ), ‖spectralKLHeightBaseTest ρ y‖^2/y := by
      exact spectralKLPhysical_dilation_real_integral (fun y : ℝ => ‖spectralKLHeightBaseTest ρ y‖^2) hq
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact spectralKLHeightBaseTest_energy ρ hy

end ArtinMatthews
