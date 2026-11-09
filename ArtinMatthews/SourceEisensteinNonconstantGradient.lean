module

public import ArtinMatthews.SourceEisensteinCuspProductTerms
public import ArtinMatthews.SourceKPAdelicEisensteinProductC1
public import ArtinMatthews.SourceHyperbolicC1Green


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine nonconstant remainder satisfies the full product gradient
identity, by subtracting the actual incoming and outgoing eigenfunctions. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix MeasureTheory OAI.CubicEisenstein
open SourceArchJacquet SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing ContDiff Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "ν" => productVolume (InfinitePlace K)

private theorem cuspInitial_re_pos {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1) : 0 < s.re := by
  have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  push_cast at hs
  linarith

theorem sourceKPAdelicNonconstantProductChart_contDiffAt {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (p : P) (hp : p ∈ U) :
    ContDiffAt ℝ 1 (sourceKPAdelicNonconstantProductChart K hζ s q) p := by
  exact (sourceKPAdelicEisensteinProductChart_contDiffAt K hζ hs q p (fun v => productUpper_pos hp v)).sub
    (((sourceKPAdelicProductSection_contDiffAt K hζ s q p (fun v => productUpper_pos hp v)).of_le
      (by simp)).add ((sourceKPAdelicOutgoingProductChart_contDiffAt K hζ (cuspInitial_re_pos K hs) q p hp).of_le
        (by simp)))

private theorem cuspProduct_value_test_integrable {ι : Type*} [Fintype ι]
    {φ f : ProductSpace ι → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι)
    (hf : ∀ p ∈ productUpper ι, ContinuousAt f p) :
    Integrable (fun p => star (φ p)*f p) (productVolume ι) := by
  apply product_density_integrable
  have hD (p : ProductSpace ι) (hp : p ∈ productUpper ι) : ContinuousAt productComplexDensity p := by
    change Tendsto (fun x : ProductSpace ι => ∏ v, ((x v 2 : ℂ)^3)⁻¹)
      (𝓝 p) (𝓝 (∏ v, ((p v 2 : ℂ)^3)⁻¹))
    apply tendsto_finsetProd
    intro v _
    have hv : Continuous (fun x : ProductSpace ι => x v 2) :=
      (EuclideanSpace.proj 2).continuous.comp (continuous_apply v)
    exact ((Complex.continuous_ofReal.comp hv).pow 3).continuousAt.inv₀
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (productUpper_pos hp v).ne'))
  have h := product_compact_star_mul_integrable hφ hc
    (F := fun p => productComplexDensity p*f p) (fun p hp =>
      (hD p (hsupp hp)).mul (hf p (hsupp hp)))
  apply h.congr
  exact Filter.Eventually.of_forall (fun p => by ring)

theorem sourceKPAdelicNonconstantProductChart_gradient_eigen {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) {φ : P → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ U) :
    (∫ p, productGradientPair φ (sourceKPAdelicNonconstantProductChart K hζ s q) p ∂ν) =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)*
        ∫ p, star (φ p)*sourceKPAdelicNonconstantProductChart K hζ s q p ∂ν := by
  let E := sourceKPAdelicEisensteinProductChart K hζ s q
  let A := sourceKPAdelicProductSection K hζ s q
  let B := sourceKPAdelicOutgoingProductChart K hζ s q
  let L := sourceArchProductCoordinateLaplacian φ
  have hs0 : 0 < s.re := cuspInitial_re_pos K hs
  have hE (p : P) (hp : p ∈ U) : ContDiffAt ℝ 1 E p :=
    sourceKPAdelicEisensteinProductChart_contDiffAt K hζ hs q p (fun v => productUpper_pos hp v)
  have hA (p : P) (hp : p ∈ U) : ContDiffAt ℝ 1 A p :=
    (sourceKPAdelicProductSection_contDiffAt K hζ s q p (fun v => productUpper_pos hp v)).of_le (by simp)
  have hB (p : P) (hp : p ∈ U) : ContDiffAt ℝ 1 B p :=
    (sourceKPAdelicOutgoingProductChart_contDiffAt K hζ hs0 q p hp).of_le (by simp)
  have hsplit (ψ : P → ℂ)
      (h₁ : Integrable (fun p => ψ p*E p) ν) (h₂ : Integrable (fun p => ψ p*A p) ν)
      (h₃ : Integrable (fun p => ψ p*B p) ν) :
      (∫ p, ψ p*sourceKPAdelicNonconstantProductChart K hζ s q p ∂ν) =
        (∫ p, ψ p*E p ∂ν) - ((∫ p, ψ p*A p ∂ν) + (∫ p, ψ p*B p ∂ν)) := by
    simp only [sourceKPAdelicNonconstantProductChart,mul_sub,mul_add]
    change (∫ p, (fun y => ψ y*E y) p - ((fun y => ψ y*A y)+(fun y => ψ y*B y)) p ∂ν) = _
    rw [integral_sub h₁ (h₂.add h₃)]
    simp only [Pi.add_apply]
    rw [integral_add h₂ h₃]
  have hl := hsplit (fun p => star (L p))
    (product_native_adjoint_integrable_C1 hE hφ hc hsupp)
    (product_native_adjoint_integrable_C1 hA hφ hc hsupp)
    (product_native_adjoint_integrable_C1 hB hφ hc hsupp)
  have hm := hsplit (fun p => star (φ p))
    (cuspProduct_value_test_integrable hφ.continuous hc hsupp (fun p hp => (hE p hp).continuousAt))
    (cuspProduct_value_test_integrable hφ.continuous hc hsupp (fun p hp => (hA p hp).continuousAt))
    (cuspProduct_value_test_integrable hφ.continuous hc hsupp (fun p hp => (hB p hp).continuousAt))
  rw [product_native_gradient_green_C1 (sourceKPAdelicNonconstantProductChart_contDiffAt K hζ hs q)
    hφ hc hsupp,hl,hm]
  dsimp only [L,E,A,B]
  rw [sourceKPAdelicEisensteinProductChart_test_eigen K hζ hs q hφ hc hsupp,
    sourceKPAdelicProductSection_test_eigen K hζ s q hφ hc hsupp,
    sourceKPAdelicOutgoingProductChart_test_eigen K hζ hs0 q hφ hc hsupp]
  ring

end
end ArtinMatthews
