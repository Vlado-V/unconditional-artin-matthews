module

public import ArtinMatthews.SourceKPResidualChartPlateau
public import ArtinMatthews.SourceKPArchProjectiveEnergy
public import ArtinMatthews.SourceHyperbolicH1CoreEnergy
public import ArtinMatthews.SourceHyperbolicProductGreen


set_option backward.privateInPublic true
@[expose] public section

/-! Stabilizer pullbacks preserve the actual native Dirichlet pairing. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators Classical
open scoped InnerProductSpace ComplexConjugate
noncomputable section

theorem h1TestGradient_inner_integral {ι : Type*} [Fintype ι] (f g : h1Tests ι 2) :
    inner ℂ (h1TestGradient f) (h1TestGradient g) =
      ∫ x, productGradientPair f.val g.val x ∂productVolume ι := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h1TestGradient_coe f, h1TestGradient_coe g] with x hf hg
  rw [hf, hg, PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [h1GradientAt_apply, RCLike.inner_apply, productGradientPair,
    map_mul, Finset.mul_sum, starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def, Complex.conj_ofReal]
  ring

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "H" => SourceKPFiniteChartStabilizer K hζ b p
local notation "Tests" => SourceKPFiniteChartTests K hζ b p
local notation "Ω" => productUpper (InfinitePlace K)
local notation "ν" => productVolume (InfinitePlace K)
local notation "R" => sourceKPFiniteChartTestPullback K hζ b p

theorem sourceKPFiniteChartTestPullback_gradient_norm (γ : H) (f : Tests) :
    ‖h1TestGradient (R γ f).val‖ = ‖h1TestGradient f.val‖ := by
  let a := sourceKPArchEuclideanAction K hζ γ.val.val
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [h1TestGradient_norm_sq, h1TestGradient_norm_sq]
  calc
    _ = ∫ x, productGradientEnergy (f.val.val ∘ a) x ∂ν := by
      apply integral_congr_ae
      filter_upwards [productVolume_ae_upper (ι := InfinitePlace K)] with x hx
      have he : (R γ f).val.val =ᶠ[𝓝 x] f.val.val ∘ a := by
        filter_upwards [(productUpper_isOpen _).mem_nhds hx] with y hy
        exact sourceKPFiniteChartTestPullback_apply K hζ b p γ f y hy
      simp only [productGradientEnergy, productPartial, he.fderiv_eq (𝕜 := ℝ)]
    _ = _ := sourceKPArchEuclideanAction_dirichlet_core K hζ γ.val.val f.val.val
      f.val.prop.1 f.val.prop.2.1 f.val.prop.2.2

theorem sourceKPFiniteChartTestPullback_gradient_inner (γ : H) (f g : Tests) :
    inner ℂ (h1TestGradient (R γ f).val) (h1TestGradient (R γ g).val) =
      inner ℂ (h1TestGradient f.val) (h1TestGradient g.val) := by
  let D : Tests →ₗ[ℂ] H1Gradient (InfinitePlace K) :=
    (h1TestGradientLinear _).comp (h1LocalTests _).subtype
  let E : Tests →ₗ[ℂ] H1Gradient (InfinitePlace K) := D.comp (R γ)
  have hn (t : Tests) : ‖E t‖ = ‖D t‖ :=
    sourceKPFiniteChartTestPullback_gradient_norm K hζ b p γ t
  change inner ℂ (E f) (E g) = inner ℂ (D f) (D g)
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (E f) (E g),
    inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (D f) (D g)]
  simp only [← E.map_smul, ← E.map_add, ← D.map_smul, ← D.map_add, ← map_sub, hn]

theorem sourceKPFiniteChartTestAverage_gradient_inner (f g : Tests)
    (hg : ∀ γ : H, R γ g = g) :
    inner ℂ (h1TestGradient (sourceKPFiniteChartTestAverage K hζ b p f).val) (h1TestGradient g.val) =
      inner ℂ (h1TestGradient f.val) (h1TestGradient g.val) := by
  let D : Tests →ₗ[ℂ] H1Gradient (InfinitePlace K) :=
    (h1TestGradientLinear _).comp (h1LocalTests _).subtype
  have hI (γ : H) : inner ℂ (D (R γ f)) (D g) = inner ℂ (D f) (D g) := by
    conv_lhs => rw [← hg γ]
    exact sourceKPFiniteChartTestPullback_gradient_inner K hζ b p γ f g
  change inner ℂ (D (sourceKPFiniteChartTestAverage K hζ b p f)) (D g) = _
  simp only [sourceKPFiniteChartTestAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, inner_smul_left, sum_inner]
  change conj ((Fintype.card H : ℂ)⁻¹) * (∑ γ : H, inner ℂ (D (R γ f)) (D g)) = _
  simp_rw [hI]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, map_inv₀, map_natCast, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  rfl

end
end ArtinMatthews
