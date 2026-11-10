module

public import ArtinMatthews.SpectralEisensteinCompactProfileSeed
public import ArtinMatthews.SpectralCuspContinuousRepresentative
public import ArtinMatthews.SpectralCuspContinuousMean
public import ArtinMatthews.SpectralCuspSeparableCoordinates
public import ArtinMatthews.SpectralCuspSmoothUnfolding
public import ArtinMatthews.SpectralEisensteinPrimitiveHorocycles
public import ArtinMatthews.SpectralHorizontalPeriodMeasurableFibers
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
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
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

/-! Integrating a primitive-width compact test window against a continuous
automorphic section extracts its literal common-period mean with the
primitive width as the horizontal measure factor. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0Invariant_primitive_profile_integral (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (hinv : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (g.val • z)=F z)
    (Y : ℝ) (hY : 0<Y) (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hpos : tsupport ρ⊆Ioi (0:ℝ))
    (hlow : ∀ y≤Y, ρ (y/(gamma0CuspTrueWidth N r:ℝ))=0) :
    let w : ℝ := gamma0CuspTrueWidth N r
    let hw : 0<w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
    let ψ := cuspHeightProfileBaseSeed w hw ρ hρ hρc hpos
    let G := fun z : UpperHalfPlane => F (r⁻¹ • z)
    (∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (G z)) =
      (w:ℂ)*∫ y, inner ℂ (ρ (y/w))
        (cuspHorizontalMean (N:ℝ) (cuspContinuousPlaneExtension Y hY G) y) ∂cuspVerticalMeasure Y := by
  dsimp only
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0<w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  let ψ := cuspHeightProfileBaseSeed w hw ρ hρ hρc hpos
  let G (z : UpperHalfPlane) := F (r⁻¹ • z)
  let E := cuspContinuousPlaneExtension Y hY G
  let H (p : ℝ × ℝ) := inner ℂ ((spectralHorizontalPartition w p.1:ℂ)*ρ (p.2/w)) (E p)
  let S := hyperbolicCuspStrip (2*w) Y
  have hG : Continuous G := hF.comp (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))
  have hS : MeasurableSet S := (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hψ (z : UpperHalfPlane) : ψ.val z=(spectralHorizontalPartition w z.re:ℂ)*ρ (z.im/w) := rfl
  have hzero (z : UpperHalfPlane) (hz : z∉S) : ψ.val z=0 := by
    rw [hψ]
    by_cases hy : Y<z.im
    · by_cases hx : 0<z.re
      · have hx' : 2*w<z.re := lt_of_not_ge (fun h => hz ⟨⟨hx,h⟩,hy⟩)
        rw [spectralHorizontalPartition_zero_right hw hx'.le,Complex.ofReal_zero,zero_mul]
      · rw [spectralHorizontalPartition_zero_left hw (le_of_not_gt hx),Complex.ofReal_zero,zero_mul]
    · rw [hlow z.im (le_of_not_gt hy),mul_zero]
  have hp (z : UpperHalfPlane) (hz : z∈S) : H (z.re,z.im)=inner ℂ (ψ.val z) (G z) := by
    have hy : Y<z.im := hz.2
    change inner ℂ ((spectralHorizontalPartition w z.re:ℂ)*ρ (z.im/w)) (E (z.re,z.im))=_
    rw [show E (z.re,z.im)=G z from cuspContinuousPlaneExtension_at_upper Y hY G z hy.le,← hψ]
  have hA : (fun z : UpperHalfPlane => H (z.re,z.im))
      =ᵐ[volume.restrict S] fun z => inner ℂ (ψ.val z) (G z) := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact hp z hz
  have hi : Integrable (fun z : UpperHalfPlane => H (z.re,z.im)) (volume.restrict S) :=
    (h2_compactSeed_inner_integrable ψ G hG).integrableOn.congr hA.symm
  have hmp := cusp_coordinates_measurePreserving (2*w) Y hY
  have hProd : Integrable H (cuspStripMeasure (2*w) Y) :=
    (hmp.integrable_comp_emb cusp_coordinates_measurableEmbedding).mp hi
  have hFiber : ∀ᵐ y ∂cuspVerticalMeasure Y,
      (∫ x, H (x,y) ∂cuspHorizontalMeasure (2*w)) =
        (w:ℂ)*inner ℂ (ρ (y/w)) (cuspHorizontalMean (N:ℝ) E y) := by
    have hgt : ∀ᵐ y ∂cuspVerticalMeasure Y, Y<y :=
      (spectralHorizontal_cuspVertical_ae_iff hY).mpr (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [hgt] with y hy
    let p (x : ℝ) := gamma0EisensteinHorizontalPoint y (hY.trans hy) x
    let U (x : ℝ) := F (r⁻¹ • p x)
    have hU : Continuous U := hG.comp (gamma0EisensteinHorizontalPoint_continuous y (hY.trans hy))
    have hperiod : Function.Periodic U w :=
      gamma0Invariant_rawCusp_primitive_period N r F hinv y (hY.trans hy)
    have hHE (x : ℝ) : H (x,y) =
        (starRingEnd ℂ) (ρ (y/w))*((spectralHorizontalPartition w x:ℂ)*U x) := by
      have hE : E (x,y)=U x := cuspContinuousPlaneExtension_at_upper Y hY G (p x) hy.le
      simp only [H,hE,RCLike.inner_apply,map_mul,Complex.conj_ofReal]
      ring
    change (∫ x in Ioc 0 (2*w), H (x,y))=_
    rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*w)]
    simp_rw [hHE]
    rw [intervalIntegral.integral_const_mul,spectralHorizontalPartition_period_integral hw U hU hperiod]
    have he := gamma0Invariant_primitive_integral_eq_common_mean N r F hF hinv y (hY.trans hy)
    rw [he,cuspContinuousPlaneExtension_mean (N:ℝ) Y (Nat.cast_nonneg N) hY G y hy]
    simp only [RCLike.inner_apply,Complex.ofReal_natCast,w]
    ring
  change (∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (G z))=
    (w:ℂ)*∫ y,inner ℂ (ρ (y/w)) (cuspHorizontalMean (N:ℝ) E y) ∂cuspVerticalMeasure Y
  calc
    _=∫ z in S, inner ℂ (ψ.val z) (G z) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => by rw [hzero z hz,inner_zero_left])).symm
    _=∫ z in S,H (z.re,z.im) := integral_congr_ae hA.symm
    _=∫ p,H p ∂cuspStripMeasure (2*w) Y := hmp.integral_comp cusp_coordinates_measurableEmbedding H
    _=∫ y, (∫ x,H (x,y) ∂cuspHorizontalMeasure (2*w)) ∂cuspVerticalMeasure Y :=
      integral_prod_symm H hProd
    _=_ := by rw [← integral_const_mul];exact integral_congr_ae hFiber

end ArtinMatthews
