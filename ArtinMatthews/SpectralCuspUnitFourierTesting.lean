module

public import ArtinMatthews.SpectralCuspUnitFourierMean
public import ArtinMatthews.SpectralCuspFourierTestSeed
public import ArtinMatthews.SpectralCuspContinuousRepresentative
public import ArtinMatthews.SpectralCuspSeparableCoordinates
public import ArtinMatthews.SpectralCuspSmoothUnfolding
public import ArtinMatthews.SpectralCuspTwoCellFourier
public import ArtinMatthews.SpectralCuspVerticalTesting
public import ArtinMatthews.SpectralEisensteinEquivalentMeans
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
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

/-! Compact Fourier tests of a continuous automorphic section. Fubini uses
the actual compact seed before the horizontal partition is removed. -/

noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace ENNReal

namespace ArtinMatthews

theorem gamma0Invariant_unit_fourier_test (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (hinv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ.val • z) = F z)
    (Y : ℝ) (hY : 0 < Y) (m : ℤ) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
    let V y := gamma0UnitCuspFourierMean N r m F (y/(gamma0CuspTrueWidth N r : ℝ))
    IntegrableOn (fun y => (ρ y/y^2) • V y) (Ioi Y) ∧
      (∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (F (r⁻¹ • z))) =
        (N : ℝ) • ∫ y in Ioi Y, (ρ y/y^2) • V y := by
  dsimp only
  let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
  let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
  let G (z : UpperHalfPlane) := F (r⁻¹ • z)
  let E := cuspContinuousPlaneExtension Y hY G
  let V y := gamma0UnitCuspFourierMean N r m F (y/(gamma0CuspTrueWidth N r : ℝ))
  let H (p : ℝ × ℝ) := (ρ p.2 : ℂ) *
    ((spectralHorizontalPartition (N : ℝ) p.1 : ℂ) * (cuspFourierPhase (N : ℝ) mN p.1 * E p))
  let S := hyperbolicCuspStrip (2*(N : ℝ)) Y
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hG : Continuous G := hF.comp (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))
  have hS : MeasurableSet S := (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hzero (z : UpperHalfPlane) (hz : z ∉ S) : ψ.val z = 0 :=
    Function.notMem_support.mp (fun h => hz (cuspFourierTestSeed_support _ _ _ _ _ _ _ Y hsρ h))
  have hp (z : UpperHalfPlane) (hz : z ∈ S) : H (z.re,z.im) = inner ℂ (ψ.val z) (G z) := by
    have hE : E (z.re,z.im) = G z := cuspContinuousPlaneExtension_at_upper Y hY G z hz.2.le
    dsimp only [H]
    rw [hE,cuspFourierTestSeed_apply]
    have hr (t : ℝ) : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    simp only [RCLike.inner_apply,map_mul,starRingEnd_apply,star_star,hr,Complex.ofReal_mul]
    ring
  have hA : (fun z : UpperHalfPlane => H (z.re,z.im))
      =ᵐ[volume.restrict S] fun z => inner ℂ (ψ.val z) (G z) := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact hp z hz
  have hi : Integrable (fun z : UpperHalfPlane => H (z.re,z.im)) (volume.restrict S) :=
    (h2_compactSeed_inner_integrable ψ G hG).integrableOn.congr hA.symm
  have hmp := cusp_coordinates_measurePreserving (2*(N : ℝ)) Y hY
  have hProd : Integrable H (cuspStripMeasure (2*(N : ℝ)) Y) :=
    (hmp.integrable_comp_emb cusp_coordinates_measurableEmbedding).mp hi
  have hFiber : (fun y => ∫ x, H (x,y) ∂cuspHorizontalMeasure (2*(N : ℝ)))
      =ᵐ[cuspVerticalMeasure Y] fun y => (N : ℂ)*((ρ y : ℂ)*V y) := by
    have hgt : ∀ᵐ y ∂cuspVerticalMeasure Y, Y < y :=
      (spectralHorizontal_cuspVertical_ae_iff hY).mpr (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [hgt] with y hy
    let U (x : ℝ) := cuspFourierPhase (N : ℝ) mN x *
      F (r⁻¹ • gamma0EisensteinHorizontalPoint y (hY.trans hy) x)
    have hU : Continuous U := ((cuspFourierPhase_contDiff _ _).continuous).mul
      (hG.comp (gamma0EisensteinHorizontalPoint_continuous y (hY.trans hy)))
    have hperiod : Function.Periodic U (N : ℝ) := fun x => by
      dsimp only [U]
      rw [cuspFourierPhase_periodic (N : ℝ) hN mN x]
      congr 1
      exact gamma0Invariant_rawCusp_horocycle_periodic N r F hinv y (hY.trans hy) x
    have hHE (x : ℝ) : H (x,y) = (ρ y : ℂ)*((spectralHorizontalPartition (N : ℝ) x : ℂ)*U x) := by
      have hE : E (x,y) = G (gamma0EisensteinHorizontalPoint y (hY.trans hy) x) :=
        cuspContinuousPlaneExtension_at_upper Y hY G
          (gamma0EisensteinHorizontalPoint y (hY.trans hy) x) hy.le
      dsimp only [H,U]
      rw [hE]
    change (∫ x in Ioc 0 (2*(N : ℝ)), H (x,y)) = _
    rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*(N : ℝ))]
    simp_rw [hHE]
    rw [intervalIntegral.integral_const_mul,spectralHorizontalPartition_period_integral hN U hU hperiod]
    have hMean := gamma0Invariant_common_fourier_integral_eq_unit N r m F hF hinv y (hY.trans hy)
    change (ρ y : ℂ)*(∫ x in (0 : ℝ)..(N : ℝ), U x) = _
    rw [show (∫ x in (0 : ℝ)..(N : ℝ),U x) = (N : ℂ)*V y from hMean]
    ring
  have hIntN : Integrable (fun y => (N : ℂ)*((ρ y : ℂ)*V y)) (cuspVerticalMeasure Y) :=
    hProd.integral_prod_right.congr hFiber
  have hInt : Integrable (fun y => (ρ y : ℂ)*V y) (cuspVerticalMeasure Y) := by
    have h := hIntN.const_mul ((N : ℂ)⁻¹)
    convert h using 1
    funext y
    rw [← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast NeZero.ne N),one_mul]
  have hInt' : Integrable (fun y => (ρ y : ℂ)*V y)
      ((cuspHorizontalMeasure 1 univ) • cuspVerticalMeasure Y) := by
    simpa only [cuspHorizontalMeasure_univ,ENNReal.ofReal_one,one_smul] using hInt
  have hDensity (y : ℝ) : (y^(-2 : ℤ)) • ((ρ y : ℂ)*V y) = (ρ y/y^2) • V y := by
    simp only [zpow_neg,zpow_ofNat,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_pow]
    ring
  have hIntegral :
      (∫ y, (ρ y : ℂ)*V y ∂cuspVerticalMeasure Y) =
        ∫ y in Ioi Y, (ρ y/y^2) • V y := by
    have h := cuspVerticalL2_integral_complex_density (w := 1) one_pos hY (fun y => (ρ y : ℂ)*V y)
    simpa only [cuspHorizontalMeasure_univ,ENNReal.ofReal_one,one_smul,hDensity] using h
  refine ⟨?_,?_⟩
  · have h := (cuspVerticalL2_integrable_complex_density_iff one_pos hY _).mp hInt'
    simpa only [hDensity] using h
  · change (∫ z : UpperHalfPlane,inner ℂ (ψ.val z) (G z)) = _
    calc
      _ = ∫ z in S,inner ℂ (ψ.val z) (G z) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun z hz => by rw [hzero z hz,inner_zero_left])).symm
      _ = ∫ z in S,H (z.re,z.im) := integral_congr_ae hA.symm
      _ = ∫ p,H p ∂cuspStripMeasure (2*(N : ℝ)) Y :=
        hmp.integral_comp cusp_coordinates_measurableEmbedding H
      _ = ∫ y,(∫ x,H (x,y) ∂cuspHorizontalMeasure (2*(N : ℝ))) ∂cuspVerticalMeasure Y :=
        integral_prod_symm H hProd
      _ = ∫ y,(N : ℂ)*((ρ y : ℂ)*V y) ∂cuspVerticalMeasure Y := integral_congr_ae hFiber
      _ = (N : ℝ) • ∫ y in Ioi Y,(ρ y/y^2) • V y := by
        rw [integral_const_mul,hIntegral,Complex.real_smul,Complex.ofReal_natCast]

end ArtinMatthews

