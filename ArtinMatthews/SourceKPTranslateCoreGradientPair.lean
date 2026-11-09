module

public import ArtinMatthews.SourceKPProductGradientPairTransport
public import ArtinMatthews.SourceKPTranslateCompactHaar


set_option backward.privateInPublic true
@[expose] public section

/-! Cross-gradient densities for two actual right translates on their
common rational quotient, with the exact Haar pullback degrees. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Filter Topology SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace ContDiff ENNReal ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "XJ" => SourceKPTranslateUpperSpace K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "C2" => sourceKPCompactC2Core K hζ
local notation "U" => SourceKPArchUpperHalfSpace K
local notation "Ω" => productUpper (InfinitePlace K)
local notation "qJ" => sourceKPTranslateUpperMk K hζ T
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "φ[" t ", " ht "]" => sourceKPFiniteRightTranslateMap K hζ T t ht
local notation "π[" t ", " ht "]" => sourceKPTranslateAutomorphicCompactMap K hζ T t ht

def sourceKPTranslateCoreGradientPairLift (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) (x : XJ) : ℂ :=
  inner ℂ (sourceKPCompactCoreGradientLift K hζ f (φ[t, ht] x.2) (sourceKPArchUpperEuclideanMap K x.1))
    (sourceKPCompactCoreGradientLift K hζ g (φ[u, hu] x.2) (sourceKPArchUpperEuclideanMap K x.1))

theorem sourceKPTranslateCoreGradientPairLift_rational (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) (γ : PGL(2,K)) (x : XJ) :
    sourceKPTranslateCoreGradientPairLift K hζ T t ht u hu f g (γ • x) =
      sourceKPTranslateCoreGradientPairLift K hζ T t ht u hu f g x := by
  let p := sourceKPArchUpperEuclideanMap K x.1
  let a := sourceKPRationalArchMap K hζ γ
  let A := sourceKPArchEuclideanAction K hζ a
  let v := sourceKPRationalFiniteMap K hζ γ
  let b := φ[t, ht] x.2
  let c := φ[u, hu] x.2
  have hp : p ∈ Ω := fun i _ => sourceArchUpperEuclideanMap_positive (x.1 i)
  have hAp : A p ∈ Ω := sourceKPArchEuclideanAction_positive K hζ a p
  have he : sourceKPArchUpperEuclideanMap K (sourceKPArchUpperAction K hζ a x.1) = A p := by
    unfold A sourceKPArchEuclideanAction p
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
  let f₀ := sourceKPCompactChartPullback K hζ f.val b
  let g₀ := sourceKPCompactChartPullback K hζ g.val c
  let f₁ := sourceKPCompactChartPullback K hζ f.val (γ • b)
  let g₁ := sourceKPCompactChartPullback K hζ g.val (γ • c)
  have hf : f₁ ∘ A =ᶠ[𝓝 p] f₀ := by
    filter_upwards [(productUpper_isOpen _).mem_nhds hp] with q hq
    exact sourceKPCompactChartPullback_rational K hζ f.val γ b q hq
  have hg : g₁ ∘ A =ᶠ[𝓝 p] g₀ := by
    filter_upwards [(productUpper_isOpen _).mem_nhds hp] with q hq
    exact sourceKPCompactChartPullback_rational K hζ g.val γ c q hq
  have hm := sourceKPArchEuclideanAction_gradientInner K hζ a f₁ g₁ p hp
    (sourceKPCompactChartPullback_differentiableAt K hζ f (γ • b) _ hAp)
    (sourceKPCompactChartPullback_differentiableAt K hζ g (γ • c) _ hAp)
  change inner ℂ (sourceProductGradientOfDifferential p (fderiv ℝ (f₁ ∘ A) p))
    (sourceProductGradientOfDifferential p (fderiv ℝ (g₁ ∘ A) p)) =
      inner ℂ (sourceProductGradientOfDifferential (A p) (fderiv ℝ f₁ (A p)))
        (sourceProductGradientOfDifferential (A p) (fderiv ℝ g₁ (A p))) at hm
  rw [hf.fderiv_eq (𝕜 := ℝ),hg.fderiv_eq (𝕜 := ℝ)] at hm
  change inner ℂ (sourceKPCompactCoreGradientLift K hζ f (φ[t, ht] (v • x.2))
      (sourceKPArchUpperEuclideanMap K (sourceKPArchUpperAction K hζ a x.1)))
    (sourceKPCompactCoreGradientLift K hζ g (φ[u, hu] (v • x.2))
      (sourceKPArchUpperEuclideanMap K (sourceKPArchUpperAction K hζ a x.1))) =
      inner ℂ (sourceKPCompactCoreGradientLift K hζ f b p) (sourceKPCompactCoreGradientLift K hζ g c p)
  rw [he,sourceKPFiniteRightTranslateMap_smul K hζ T t ht v x.2,
    sourceKPFiniteRightTranslateMap_smul K hζ T u hu v x.2]
  exact hm.symm

def sourceKPTranslateCoreGradientPair (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) : YJ → ℂ :=
  Quotient.lift (sourceKPTranslateCoreGradientPairLift K hζ T t ht u hu f g) (by
    intro x y hxy
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hxy
    rw [← hγ]
    exact sourceKPTranslateCoreGradientPairLift_rational K hζ T t ht u hu f g γ y)

theorem sourceKPTranslateCoreGradientPair_upper (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) (x : XJ) :
    sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g (qJ x) =
      inner ℂ (sourceKPCompactCoreGradientLift K hζ f (φ[t, ht] x.2) (sourceKPArchUpperEuclideanMap K x.1))
        (sourceKPCompactCoreGradientLift K hζ g (φ[u, hu] x.2) (sourceKPArchUpperEuclideanMap K x.1)) := rfl

theorem sourceKPTranslateCoreGradientPair_conj_swap (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) (y : YJ) :
    conj (sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g y) =
      sourceKPTranslateCoreGradientPair K hζ T u hu t ht g f y := by
  induction y using Quotient.inductionOn with
  | _ x =>
    change conj (sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g (qJ x)) =
      sourceKPTranslateCoreGradientPair K hζ T u hu t ht g f (qJ x)
    simp only [sourceKPTranslateCoreGradientPair_upper]
    exact inner_conj_symm _ _

private theorem gradientLift_upper_continuous (f : C2) (b : SourceKPFiniteLevelFiber K hζ) :
    Continuous (fun p : U => sourceKPCompactCoreGradientLift K hζ f b (sourceKPArchUpperEuclideanMap K p)) := by
  have hd := sourceProductGradientOfDifferential_continuousOn (sourceKPCompactChartPullback K hζ f.val b)
    ((f.prop.2.2 b).of_le (by norm_num))
  simpa only [sourceKPCompactCoreGradientLift_differential,Function.comp_def] using
    hd.comp_continuous (sourceKPArchUpperEuclideanMap_continuous K)
      (fun p i _ => sourceArchUpperEuclideanMap_positive (p i))

theorem sourceKPTranslateCoreGradientPair_continuous (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) : Continuous (sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g) := by
  have hc : Continuous (sourceKPTranslateCoreGradientPairLift K hζ T t ht u hu f g) := by
    apply continuous_prod_of_discrete_right.mpr
    intro c
    exact (gradientLift_upper_continuous K hζ f (φ[t, ht] c)).inner
      (gradientLift_upper_continuous K hζ g (φ[u, hu] c))
  exact hc.quotient_lift _

private theorem energy_map_integrable (t : Gf) (ht : J ≤ D t) (f : C2) :
    Integrable (sourceKPCompactCoreEnergy K hζ f) (Measure.map π[t, ht] μJ) := by
  rw [sourceKPTranslateAutomorphicCompactMap_haar]
  exact (sourceKPCompactCoreEnergy_integrable K hζ f).smul_measure (ENNReal.natCast_ne_top _)

theorem sourceKPTranslateCoreEnergy_pullback_integrable (t : Gf) (ht : J ≤ D t) (f : C2) :
    Integrable (fun y => sourceKPCompactCoreEnergy K hζ f (π[t, ht] y)) μJ :=
  (⟨(sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t ht).measurable,rfl⟩ :
    MeasurePreserving π[t, ht] μJ (Measure.map π[t, ht] μJ)).integrable_comp_of_integrable
      (energy_map_integrable K hζ T t ht f)

theorem sourceKPTranslateCoreEnergy_pullback_integral (t : Gf) (ht : J ≤ D t) (f : C2) :
    (∫ y, sourceKPCompactCoreEnergy K hζ f (π[t, ht] y) ∂μJ) =
      ((J).relIndex (D t) : ℝ)*(∫ y, sourceKPCompactCoreEnergy K hζ f y ∂μY) := by
  have hp := (sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t ht).measurable
  rw [← integral_map hp.aemeasurable (energy_map_integrable K hζ T t ht f).aestronglyMeasurable,
    sourceKPTranslateAutomorphicCompactMap_haar,integral_smul_measure]
  simp only [ENNReal.toReal_natCast,smul_eq_mul]

theorem sourceKPTranslateCoreGradientPair_norm_le (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) (r : ℝ) (hr : 0 < r) (y : YJ) :
    ‖sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g y‖ ≤
      (r*sourceKPCompactCoreEnergy K hζ f (π[t, ht] y) + r⁻¹*sourceKPCompactCoreEnergy K hζ g (π[u, hu] y))/2 := by
  induction y using Quotient.inductionOn with
  | _ x =>
    change ‖sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g (qJ x)‖ ≤
      (r*sourceKPCompactCoreEnergy K hζ f (π[t, ht] (qJ x)) +
        r⁻¹*sourceKPCompactCoreEnergy K hζ g (π[u, hu] (qJ x)))/2
    rw [sourceKPTranslateCoreGradientPair_upper,
      sourceKPTranslateAutomorphicCompactMap_upperMk K hζ T t ht,
      sourceKPTranslateAutomorphicCompactMap_upperMk K hζ T u hu,
      sourceKPCompactCoreEnergy_chart,sourceKPCompactCoreEnergy_chart,
      ← sourceKPCompactCoreGradientLift_norm_sq,← sourceKPCompactCoreGradientLift_norm_sq]
    let A := sourceKPCompactCoreGradientLift K hζ f (φ[t, ht] x.2) (sourceKPArchUpperEuclideanMap K x.1)
    let B := sourceKPCompactCoreGradientLift K hζ g (φ[u, hu] x.2) (sourceKPArchUpperEuclideanMap K x.1)
    change ‖inner ℂ A B‖ ≤ (r*‖A‖^2+r⁻¹*‖B‖^2)/2
    refine (norm_inner_le_norm (𝕜 := ℂ) A B).trans ?_
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    refine le_of_mul_le_mul_left ?_ hr
    rw [mul_add,← mul_assoc r r⁻¹,mul_inv_cancel₀ hr.ne',one_mul]
    nlinarith only [sq_nonneg (r*‖A‖-‖B‖)]

theorem sourceKPTranslateCoreGradientPair_norm_le_half_sum (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) (y : YJ) :
    ‖sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g y‖ ≤
      (sourceKPCompactCoreEnergy K hζ f (π[t, ht] y)+sourceKPCompactCoreEnergy K hζ g (π[u, hu] y))/2 := by
  simpa only [one_mul,inv_one] using sourceKPTranslateCoreGradientPair_norm_le K hζ T t ht u hu f g 1 one_pos y

theorem sourceKPTranslateCoreGradientPair_integrable (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) : Integrable (sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g) μJ := by
  have hm := ((sourceKPTranslateCoreEnergy_pullback_integrable K hζ T t ht f).add
    (sourceKPTranslateCoreEnergy_pullback_integrable K hζ T u hu g)).div_const 2
  exact hm.mono' (sourceKPTranslateCoreGradientPair_continuous K hζ T t ht u hu f g).aestronglyMeasurable
    (ae_of_all μJ (sourceKPTranslateCoreGradientPair_norm_le_half_sum K hζ T t ht u hu f g))

end
end ArtinMatthews
