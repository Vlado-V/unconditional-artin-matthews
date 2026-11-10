module

public import ArtinMatthews.SourceHyperbolicFlatCoordinates
public import ArtinMatthews.SourceHyperbolicNativeCoefficient
public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SchwartzGradient
public import ArtinMatthews.SourceKPAutomorphicSpectralContinuation
public import ArtinMatthews.SourceKPCompactFormLocalization
public import ArtinMatthews.SourceKPResidualChartPlateau
public import ArtinMatthews.SourceHyperbolicProductMeasureGreen
public import ArtinMatthews.SourceKPResidualNativeWeak
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

/-! The actual native weak pairing with ordinary Cartesian gradients and Lebesgue measure. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen HilbertResolvent
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators Classical
open scoped SchwartzMap ContDiff InnerProductSpace ComplexConjugate
noncomputable section

private theorem productNativeDiagonal_inner {ι : Type*} [Fintype ι]
    (a : ι × Fin 3 → ℝ) (u v : H1Vector ι) :
    inner ℂ (productNativeDiagonal a u) v = inner ℂ u (productNativeDiagonal a v) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [productNativeDiagonal_apply, RCLike.inner_apply, map_mul, starRingEnd_apply]
  rw [Complex.star_def, Complex.conj_ofReal]
  ring

private theorem productNative_real_inner {ι : Type*} [Fintype ι] (u v : H1Vector ι) :
    inner ℝ u v = (inner ℂ u v).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
  rfl

theorem productNativeCoefficient_coercive {ι : Type*} [Fintype ι]
    {x : ProductSpace ι} (hx : x ∈ productUpper ι) :
    ∃ c > 0, ∀ w : H1Vector ι, c*‖w‖*‖w‖ ≤ inner ℝ (productNativeCoefficient x w) w := by
  obtain ⟨c,hc,h⟩ := productNativeDiagonal_coercive
    (fun ij : ι × Fin 3 => productNativeDensity x * (x ij.1 2)^2)
    (fun ij => mul_pos (productNativeDensity_pos hx) (pow_pos (productUpper_pos hx ij.1) 2))
  refine ⟨c,hc,fun w => ?_⟩
  rw [productNative_real_inner]
  exact h w

private theorem productNativeCoefficient_inner_unweight {ι : Type*} [Fintype ι]
    {x : ProductSpace ι} (hx : x ∈ productUpper ι) (u v : H1Vector ι) :
    inner ℝ (productNativeCoefficient x (productNativeUnweight x u)) v =
      productNativeDensity x * (inner ℂ (productNativeDiagonal (fun ij => x ij.1 2) v) u).re := by
  have hcomp : productNativeCoefficient x (productNativeUnweight x u) =
      (productNativeDensity x : ℂ) • productNativeDiagonal (fun ij => x ij.1 2) u := by
    ext ij
    simp only [productNativeCoefficient, productNativeUnweight, productNativeDiagonal_apply,
      PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr (productUpper_pos hx ij.1).ne']
  rw [hcomp, productNative_real_inner, inner_smul_left, productNativeDiagonal_inner]
  change ((star (productNativeDensity x : ℂ)) *
      inner ℂ u (productNativeDiagonal (fun ij => x ij.1 2) v)).re = _
  rw [Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
  exact congrArg (productNativeDensity x * ·)
    (inner_re_symm (𝕜 := ℂ) u (productNativeDiagonal (fun ij => x ij.1 2) v))

private theorem productVolume_integral_density_on {ι : Type*} [Fintype ι]
    {V : Set (ProductSpace ι)} (hV : MeasurableSet V) (hVu : V ⊆ productUpper ι)
    (f : ProductSpace ι → ℝ) (h0 : ∀ x ∉ V, f x = 0) :
    (∫ x, f x ∂productVolume ι) = ∫ x in V, productNativeDensity x * f x := by
  rw [productVolume_eq_density, integral_withDensity_eq_integral_toReal_smul
    (productDensity_measurable ι) (Eventually.of_forall productDensity_lt_top)]
  have hvan (x : ProductSpace ι) (hx : x ∉ V) :
      (productDensity x).toReal • f x = 0 := by rw [h0 x hx, smul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume.restrict (productUpper ι)) hvan,
    Measure.restrict_restrict_of_subset hVu]
  apply setIntegral_congr_fun hV
  intro x hx
  change (productDensity x).toReal • f x = productNativeDensity x * f x
  rw [productNativeDensity_toReal (hVu hx), smul_eq_mul]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "I" => InfinitePlace K
local notation "X" => ProductSpace I
local notation "E" => EuclideanSpace ℝ (I × Fin 3)
local notation "e" => productFlatEuclideanEquiv I
local notation "basis" => EuclideanSpace.basisFun (I × Fin 3) ℝ
local notation "Ω" => productUpper I
local notation "ν" => productVolume I
local notation "V" => sourceKPResidualChartPlateauDomain K hζ b p
local notation "H" => SourceKPFiniteChartStabilizer K hζ b p
local notation "Tests" => SourceKPFiniteChartTests K hζ b p
local notation "L" => sourceKPCompactH1Localization K hζ b p
local notation "M" => h1EnergyMass I
local notation "G" => h1EnergyGradient I
local notation "r" => exceptionalCenter (InfinitePlace.nrComplexPlaces K : ℝ)
local notation "Rform" => sourceKPAutomorphicExceptionalFormResidue K hζ
local notation "ordinary" => SchwartzGradient.CM.Construction.schwartzOrdinaryGradient basis

theorem sourceKPResidualLocalized_cartesian_weak {T : ℝ} (hT : 1 ≤ T) (η : Tests)
    (hηinv : ∀ (γ : H) (x : X), x ∈ Ω →
      η.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x) = η.val.val x)
    {W : Set Y} (hW : IsOpen W) (hη : ∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1)
    (m : Lp ℂ 2 (volume : Measure E)) (g : Lp (H1Vector I) 2 (volume : Measure E))
    (hmg : ∀ᵐ x ∂(volume : Measure X).restrict (V W),
      m (e x) = M (L η (Rform hT).val) x ∧
        g (e x) = productNativeUnweight x (G (L η (Rform hT).val) x))
    (ψ : 𝓢(E, ℂ)) (hψc : HasCompactSupport (ψ : E → ℂ)) (hψ : tsupport ψ ⊆ e '' V W) :
    (∫ z, inner ℝ (productNativeCoefficient ((e).symm z) (g z)) (ordinary ψ z)) =
      ∫ z, inner ℝ (((r * productNativeDensity ((e).symm z) : ℝ) : ℂ) • m z) (ψ z) := by
  let M₀ := M (L η (Rform hT).val)
  let G₀ := G (L η (Rform hT).val)
  have hV := sourceKPResidualChartPlateauDomain_isOpen K hζ b p hW
  have hVupper : V W ⊆ Ω :=
    Set.inter_subset_left.trans (sourceKPFiniteChartCoordinateDomain_upper K hζ b p)
  have hφs : tsupport ((ψ : E → ℂ) ∘ e) ⊆ V W := by
    change tsupport ((ψ : E → ℂ) ∘ (e).toHomeomorph) ⊆ V W
    rw [tsupport_comp_eq_preimage _ (e).toHomeomorph]
    intro x hx
    obtain ⟨y,hy,he⟩ := hψ hx
    exact (e).injective he ▸ hy
  let φ : h1Tests I 2 :=
    ⟨(ψ : E → ℂ) ∘ e, (ψ.smooth 2).comp (e).contDiff,
      hψc.comp_homeomorph (e).toHomeomorph, hφs.trans hVupper⟩
  have hweak := sourceKPResidualLocalized_weak_eigen K hζ b p hT η hηinv hW hη φ hφs
  change inner ℂ (h1TestGradient φ) G₀ = (r : ℂ) * inner ℂ (h1TestMass φ) M₀ at hweak
  have hre := congrArg Complex.re hweak
  simp only [L2.inner_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  have hGr := integral_re (L2.integrable_inner (𝕜 := ℂ) (h1TestGradient φ) G₀)
  have hMr := integral_re (L2.integrable_inner (𝕜 := ℂ) (h1TestMass φ) M₀)
  simp only [RCLike.re_eq_complex_re] at hGr hMr
  rw [← hGr, ← hMr] at hre
  let F (x : X) := (inner ℂ (h1GradientAt φ x) (G₀ x)).re
  let J (x : X) := (inner ℂ (φ.val x) (M₀ x)).re
  have hF0 (x : X) (hx : x ∉ V W) : F x = 0 := by
    have hg := image_eq_zero_of_notMem_tsupport
      (fun hs => hx (hφs (h1GradientAt_support φ hs)))
    simp only [F, hg, inner_zero_left, Complex.zero_re]
  have hJ0 (x : X) (hx : x ∉ V W) : J x = 0 := by
    have hz : φ.val x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hφs hs))
    change (inner ℂ (φ.val x) (M₀ x)).re = 0
    rw [hz, inner_zero_left, Complex.zero_re]
  have hreal : (∫ x, F x ∂ν) = r * ∫ x, J x ∂ν := by
    calc
      _ = ∫ x, (inner ℂ ((h1TestGradient φ) x) (G₀ x)).re ∂ν := by
        apply integral_congr_ae
        filter_upwards [h1TestGradient_coe φ] with x hx
        simp only [F, hx]
      _ = r * ∫ x, (inner ℂ ((h1TestMass φ) x) (M₀ x)).re ∂ν := hre
      _ = _ := by
        apply congrArg (r * ·)
        apply integral_congr_ae
        filter_upwards [h1TestMass_coe φ] with x hx
        simp only [J, hx]
  rw [productVolume_integral_density_on hV.measurableSet hVupper F hF0,
    productVolume_integral_density_on hV.measurableSet hVupper J hJ0] at hreal
  let AE (z : E) := inner ℝ (productNativeCoefficient ((e).symm z) (g z)) (ordinary ψ z)
  let ME (z : E) := inner ℝ (((r * productNativeDensity ((e).symm z) : ℝ) : ℂ) • m z) (ψ z)
  change (∫ z, AE z) = ∫ z, ME z
  have hmp := productFlatEuclideanEquiv_measurePreserving I
  have hme := (e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← hmp.integral_comp hme AE, ← hmp.integral_comp hme ME]
  have hψout (x : X) (hx : x ∉ V W) : e x ∉ tsupport ψ := by
    intro hz
    obtain ⟨y,hy,he⟩ := hψ hz
    exact hx ((e).injective he ▸ hy)
  have hAE0 (x : X) (hx : x ∉ V W) : AE (e x) = 0 := by
    change inner ℝ (productNativeCoefficient ((e).symm (e x)) (g (e x))) (ordinary ψ (e x)) = 0
    rw [SchwartzGradient.CM.Construction.schwartzOrdinaryGradient_zero basis ψ (hψout x hx),
      inner_zero_right]
  have hME0 (x : X) (hx : x ∉ V W) : ME (e x) = 0 := by
    have hz : ψ (e x) = 0 := image_eq_zero_of_notMem_tsupport (hψout x hx)
    change inner ℝ (((r * productNativeDensity ((e).symm (e x)) : ℝ) : ℂ) • m (e x)) (ψ (e x)) = 0
    rw [hz, inner_zero_right]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hAE0,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hME0]
  have hφe : φ.val ∘ (e).symm = (ψ : E → ℂ) := by
    funext z
    simp only [φ, Function.comp_apply, (e).apply_symm_apply]
  have hgrad (x : X) : h1GradientAt φ x =
      productNativeDiagonal (fun ij => x ij.1 2) (ordinary ψ (e x)) := by
    ext ij
    have hd := productFlatEuclideanEquiv_partial I φ.val x
      (φ.prop.1.differentiable (by norm_num) x) ij.1 ij.2
    rw [hφe] at hd
    rw [h1GradientAt_apply, productNativeDiagonal_apply,
      SchwartzGradient.CM.Construction.schwartzOrdinaryGradient_apply,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, hd]
  calc
    _ = ∫ x in V W, productNativeDensity x * F x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hV.measurableSet, hmg] with x hx h
      change inner ℝ (productNativeCoefficient ((e).symm (e x)) (g (e x))) (ordinary ψ (e x)) = _
      rw [(e).symm_apply_apply, h.2, productNativeCoefficient_inner_unweight (hVupper hx)]
      change _ = productNativeDensity x * (inner ℂ (h1GradientAt φ x) (G₀ x)).re
      rw [hgrad]
    _ = r * ∫ x in V W, productNativeDensity x * J x := hreal
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hmg] with x h
      change r * (productNativeDensity x * (inner ℂ (φ.val x) (M₀ x)).re) = ME (e x)
      change _ = inner ℝ (((r * productNativeDensity ((e).symm (e x)) : ℝ) : ℂ) • m (e x)) (ψ (e x))
      rw [(e).symm_apply_apply, h.1]
      change _ = (inner ℂ (((r * productNativeDensity x : ℝ) : ℂ) • M₀ x) (φ.val x)).re
      rw [inner_smul_left]
      change _ = ((star ((r * productNativeDensity x : ℝ) : ℂ)) * inner ℂ (M₀ x) (φ.val x)).re
      have hi : (inner ℂ (M₀ x) (φ.val x)).re = (inner ℂ (φ.val x) (M₀ x)).re :=
        by simpa only [RCLike.re_eq_complex_re] using (inner_re_symm (𝕜 := ℂ) (M₀ x) (φ.val x))
      rw [Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul, hi, mul_assoc]

end
end ArtinMatthews
