module

public import ArtinMatthews.SourceKPArchRadialMeasure
public import ArtinMatthews.SourceHyperbolicHardyEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Differentiation and energy of the literal common vertical dilation. -/
namespace ArtinMatthews
open NumberField OAI.CubicEisenstein SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def productRadialVector (p : ProductSpace ι) : ProductSpace ι :=
  ∑ i, p i 2 • productDirection i 2

theorem productRadialVector_apply (p : ProductSpace ι) (i : ι) :
    productRadialVector p i = p i 2 • euclideanCoordinateVector 2 := by
  unfold productRadialVector
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp [productDirection]
  · intro j _ hji
    simp [productDirection, Pi.single_apply, hji, Ne.symm hji]
  · simp

theorem productRadial_eq_fderiv_vector (f : ProductSpace ι → ℂ) (p : ProductSpace ι) :
    productRadial f p = fderiv ℝ f p (productRadialVector p) := by
  simp only [productRadial, productVertical, productPartial, productRadialVector,
    map_sum, map_smul, Complex.real_smul]

theorem productRadial_norm_sq_le_gradient (f : ProductSpace ι → ℂ) (p : ProductSpace ι) :
    ‖productRadial f p‖^2 ≤ (Fintype.card ι : ℝ) * productGradientEnergy f p := by
  have hnorm : ‖productRadial f p‖ ≤ ∑ i, ‖productVertical f i p‖ :=
    norm_sum_le _ _
  have hCS : (∑ i, ‖productVertical f i p‖)^2 ≤
      (Fintype.card ι : ℝ) * productVerticalEnergy f p := by
    simpa [productVerticalEnergy] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ))
        (fun i => ‖productVertical f i p‖))
  calc
    _ ≤ (∑ i, ‖productVertical f i p‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (Fintype.card ι : ℝ) * productVerticalEnergy f p := hCS
    _ ≤ _ := mul_le_mul_of_nonneg_left (productVerticalEnergy_le_gradientEnergy f p)
      (Nat.cast_nonneg _)

variable (K : Type) [Field K] [NumberField K]

def sourceKPArchRadialEuclideanCurve (q : SourceKPArchUpperHalfSpace K) (t : ℝ) :
    ProductSpace (InfinitePlace K) :=
  sourceKPArchUpperEuclideanMap K (sourceKPArchRadialPoint K t q)

theorem sourceKPArchRadialEuclideanCurve_coordinates (q : SourceKPArchUpperHalfSpace K) (t : ℝ) :
    sourceKPArchRadialEuclideanCurve K q t =
      sourceKPArchUpperEuclideanMap K q + (Real.exp t-1) •
        productRadialVector (sourceKPArchUpperEuclideanMap K q) := by
  ext i j
  fin_cases j <;>
    simp [sourceKPArchRadialEuclideanCurve, sourceKPArchRadialPoint, sourceArchRadialPoint,
      sourceKPArchUpperEuclideanMap, sourceArchUpperEuclideanMap, sourceArchUpperEmbedding,
      sourceArchSpatialCoordinates_symm_apply, productRadialVector_apply, euclideanCoordinateVector]
  all_goals ring

theorem sourceKPArchRadialEuclideanCurve_vector (q : SourceKPArchUpperHalfSpace K) (t : ℝ) :
    productRadialVector (sourceKPArchRadialEuclideanCurve K q t) =
      Real.exp t • productRadialVector (sourceKPArchUpperEuclideanMap K q) := by
  ext i j
  simp [sourceKPArchRadialEuclideanCurve, sourceKPArchRadialPoint, sourceArchRadialPoint,
    sourceKPArchUpperEuclideanMap, sourceArchUpperEuclideanMap, sourceArchUpperEmbedding,
    sourceArchSpatialCoordinates_symm_apply, productRadialVector_apply, mul_assoc]

theorem sourceKPArchRadialEuclideanCurve_hasDerivAt (q : SourceKPArchUpperHalfSpace K) (t : ℝ) :
    HasDerivAt (sourceKPArchRadialEuclideanCurve K q)
      (productRadialVector (sourceKPArchRadialEuclideanCurve K q t)) t := by
  let p := sourceKPArchUpperEuclideanMap K q
  have he : sourceKPArchRadialEuclideanCurve K q =
      fun s => p + (Real.exp s-1) • productRadialVector p :=
    funext (sourceKPArchRadialEuclideanCurve_coordinates K q)
  rw [sourceKPArchRadialEuclideanCurve_vector, he]
  simpa only [zero_add] using!
    (hasDerivAt_const t p).add (((Real.hasDerivAt_exp t).sub_const 1).smul_const (productRadialVector p))

theorem sourceKPArchRadialEuclideanCurve_positive (q : SourceKPArchUpperHalfSpace K) (t : ℝ) :
    sourceKPArchRadialEuclideanCurve K q t ∈ productUpper (InfinitePlace K) :=
  fun i _ => sourceArchUpperEuclideanMap_positive (sourceKPArchRadialPoint K t q i)

theorem sourceKPArchRadialEuclideanTest_hasDerivAt
    {f : ProductSpace (InfinitePlace K) → ℂ}
    (hf : ContDiffOn ℝ 1 f (productUpper (InfinitePlace K)))
    (q : SourceKPArchUpperHalfSpace K) (t : ℝ) :
    HasDerivAt (fun s => f (sourceKPArchRadialEuclideanCurve K q s))
      (productRadial f (sourceKPArchRadialEuclideanCurve K q t)) t := by
  have hp := sourceKPArchRadialEuclideanCurve_positive K q t
  have hd := ((hf _ hp).contDiffAt ((productUpper_isOpen (InfinitePlace K)).mem_nhds hp)).differentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have h := hd.hasFDerivAt.comp_hasDerivAt t (sourceKPArchRadialEuclideanCurve_hasDerivAt K q t)
  rw [productRadial_eq_fderiv_vector]
  simpa only [Function.comp_def] using h

end
end ArtinMatthews
