module

public import ArtinMatthews.SourcePrincipalContourIntegrals
public import ArtinMatthews.SourcePoissonInitialFormula
public import ArtinMatthews.SourcePrincipalContourFubini
public import ArtinMatthews.SourcePrincipalContourGeometry
public import ArtinMatthews.SourcePrincipalInitialShifts
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

/-! The pointwise pole-free shifts act on the entire actual principal integral. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Set MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "σ₁" => sourcePrincipalSigma
local notation "z₁" => sourcePrincipalZetaLine

theorem sourcePrincipalPoissonIntegral_initial_shift
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    sourcePrincipalPoissonIntegral F hζ S₀ η v X Y Z 4 4 2 =
      sourcePrincipalPoissonIntegral F hζ S₀ η v X Y Z σ₁ σ₁ z₁ := by
  let K := sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z
  let I := sourcePrincipalPoissonIntegral F hζ S₀ η v X Y Z
  have hσ₄ := sourcePrincipalSigma_le_four
  have hz₂ := sourcePrincipalZetaLine_mem.2
  have hI {a b c : ℝ} (ha : σ₁ ≤ a) (hb : b ∈ Icc σ₁ 4) (hc : c ∈ Icc z₁ 2) :
      Integrable (K a b c) sourcePoissonHeightMeasure := by
    have hw : b ∈ Icc (95 / 100 : ℝ) 4 :=
      ⟨(by norm_num [sourcePrincipalSigma] : (95 / 100 : ℝ) ≤ σ₁).trans hb.1, hb.2⟩
    have hz : c ∈ Icc (16 / 100 : ℝ) 2 := ⟨sourcePrincipalZetaLine_mem.1.trans hc.1, hc.2⟩
    obtain ⟨_, _, h⟩ := sourcePrincipalPoissonIntegral_integrable_and_bound F hζ S₀ η v hJ hcut ha hw hz
      (sourcePrincipalSigma_gt_one.trans_le hb.1).ne' (sourcePrincipalZetaLine_gt_sixth.trans_le hc.1).ne'
    exact (h hX hY hZ).1
  have hi0 := hI hσ₄ ⟨hσ₄, le_rfl⟩ ⟨hz₂, le_rfl⟩
  have hi1 := hI hσ₄ ⟨hσ₄, le_rfl⟩ ⟨le_rfl, hz₂⟩
  have hi2 := hI hσ₄ ⟨le_rfl, hσ₄⟩ ⟨le_rfl, hz₂⟩
  have hi3 := hI le_rfl ⟨le_rfl, hσ₄⟩ ⟨le_rfl, hz₂⟩
  calc
    I 4 4 2 = I 4 4 z₁ := by
      change sourcePoissonNormalization ^ 3 * (∫ p, K 4 4 2 p ∂sourcePoissonHeightMeasure) =
        sourcePoissonNormalization ^ 3 * (∫ p, K 4 4 z₁ p ∂sourcePoissonHeightMeasure)
      rw [sourcePoissonHeight_integral_iterated _ hi0, sourcePoissonHeight_integral_iterated _ hi1]
      apply congrArg (fun a : ℂ => sourcePoissonNormalization ^ 3 * a)
      apply integral_congr_ae
      filter_upwards with u
      apply integral_congr_ae
      filter_upwards with t
      exact (sourcePrincipalPoissonInitialShifts_pointwise F hζ S₀ η v hJ hcut hX hY hZ u t 0).1
    _ = I 4 σ₁ z₁ := by
      change sourcePoissonNormalization ^ 3 * (∫ p, K 4 4 z₁ p ∂sourcePoissonHeightMeasure) =
        sourcePoissonNormalization ^ 3 * (∫ p, K 4 σ₁ z₁ p ∂sourcePoissonHeightMeasure)
      rw [sourcePrincipalHeight_integral_w_last _ hi1, sourcePrincipalHeight_integral_w_last _ hi2]
      apply congrArg (fun a : ℂ => sourcePoissonNormalization ^ 3 * a)
      apply integral_congr_ae
      filter_upwards with u
      apply integral_congr_ae
      filter_upwards with y
      exact (sourcePrincipalPoissonInitialShifts_pointwise F hζ S₀ η v hJ hcut hX hY hZ u 0 y).2.1
    _ = I σ₁ σ₁ z₁ := by
      change sourcePoissonNormalization ^ 3 * (∫ p, K 4 σ₁ z₁ p ∂sourcePoissonHeightMeasure) =
        sourcePoissonNormalization ^ 3 * (∫ p, K σ₁ σ₁ z₁ p ∂sourcePoissonHeightMeasure)
      rw [sourcePrincipalHeight_integral_xi_last _ hi2, sourcePrincipalHeight_integral_xi_last _ hi3]
      apply congrArg (fun a : ℂ => sourcePoissonNormalization ^ 3 * a)
      apply integral_congr_ae
      filter_upwards with t
      apply integral_congr_ae
      filter_upwards with y
      exact (sourcePrincipalPoissonInitialShifts_pointwise F hζ S₀ η v hJ hcut hX hY hZ 0 t y).2.2

end
end ArtinMatthews.SourceEulerAssembly
