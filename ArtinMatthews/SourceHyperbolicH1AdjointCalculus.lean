module

public import ArtinMatthews.SourceHyperbolicH1Tests
public import ArtinMatthews.SourceHyperbolicHardyCalculus


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def h1Coordinate (f : ProductSpace ι → ℂ) (i : ι) (j : Fin 3) (p : ProductSpace ι) : ℂ :=
  (p i 2 : ℂ) * productPartial f i j p

def h1CoordinateAdjoint (φ : ProductSpace ι → ℂ) (i : ι) (j : Fin 3) (p : ProductSpace ι) : ℂ :=
  2 * (euclideanCoordinateVector j 2 : ℂ) * φ p - h1Coordinate φ i j p

theorem h1WeightedValue_derivative {φ : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hφ : ContDiffAt ℝ 1 φ p) (hp : p ∈ productUpper ι) (i : ι) (j : Fin 3) :
    productPartial (productWeightedValue φ i) i j p =
      -(productComplexDensity p * h1CoordinateAdjoint φ i j p) := by
  have hF := (hφ.differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt (productDirection i j)
  have hH := ((productHeightCLM i).hasFDerivAt (x := p)).hasLineDerivAt (productDirection i j)
  change HasDerivAt (fun t : ℝ => φ (p+t • productDirection i j)) (productPartial φ i j p) 0 at hF
  change HasDerivAt (fun t : ℝ => productHeightCLM i (p+t • productDirection i j))
    (productHeightCLM i (productDirection i j)) 0 at hH
  have hn : (productHeightCLM i (p+(0 : ℝ) • productDirection i j))^2 ≠ 0 := by
    simpa only [zero_smul,add_zero,productHeightCLM_apply] using
      pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne')
  have h := (hF.div (hH.pow 2) hn).const_mul (otherWeight i p)
  have hline : HasLineDerivAt ℝ (productWeightedValue φ i)
      (otherWeight i p *
        (productPartial φ i j p * (p i 2 : ℂ)^2 -
          φ p * (2 * (p i 2 : ℂ) * (euclideanCoordinateVector j 2 : ℂ))) /
        ((p i 2 : ℂ)^2)^2) p (productDirection i j) := by
    simp only [HasLineDerivAt, productWeightedValue]
    simp_rw [otherWeight_on_line]
    simpa only [Pi.div_apply,zero_smul,add_zero,productHeightCLM_apply,
      productDirection,Pi.single_eq_same,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_div_assoc] using! h
  have he := (((productWeightedValue_contDiffAt hφ hp i).differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt
    (productDirection i j)).unique hline
  change productPartial (productWeightedValue φ i) i j p = _ at he
  rw [he,productComplexDensity_factor p i]
  unfold h1CoordinateAdjoint h1Coordinate
  field_simp [Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne']
  ring

theorem h1WeightedValue_support (φ : ProductSpace ι → ℂ) (i : ι) :
    tsupport (productWeightedValue φ i) ⊆ tsupport φ := by
  unfold productWeightedValue
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left.trans tsupport_mul_subset_right

theorem h1WeightedValue_contDiff (φ : h1Tests ι 2) (i : ι) :
    ContDiff ℝ 1 (productWeightedValue φ.val i) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ productUpper ι
  · exact productWeightedValue_contDiffAt (φ.prop.1.of_le (by norm_num)).contDiffAt hp i
  · have hn : p ∉ tsupport (productWeightedValue φ.val i) :=
      fun h => hp (φ.prop.2.2 (h1WeightedValue_support φ.val i h))
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ProductSpace ι => (0 : ℂ)) p).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem h1WeightedValue_compact (φ : h1Tests ι 2) (i : ι) :
    HasCompactSupport (productWeightedValue φ.val i) :=
  φ.prop.2.1.of_isClosed_subset (isClosed_tsupport _) (h1WeightedValue_support φ.val i)

theorem h1CoordinateAdjoint_contDiff (φ : h1Tests ι 2) (i : ι) (j : Fin 3) :
    ContDiff ℝ 1 (h1CoordinateAdjoint φ.val i j) := by
  have hD : ContDiff ℝ 1 (productPartial φ.val i j) :=
    (φ.prop.1.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hφ : ContDiff ℝ 1 φ.val := φ.prop.1.of_le (by norm_num)
  have hc : ContDiff ℝ 1 (fun p => 2 * (euclideanCoordinateVector j 2 : ℂ) * φ.val p) :=
    contDiff_const.mul hφ
  exact hc.sub ((productHeightCLM i).contDiff.mul hD)

omit [Fintype ι] in
theorem h1CoordinateAdjoint_support (φ : ProductSpace ι → ℂ) (i : ι) (j : Fin 3) :
    tsupport (h1CoordinateAdjoint φ i j) ⊆ tsupport φ := by
  unfold h1CoordinateAdjoint h1Coordinate
  refine (tsupport_sub _ _).trans (Set.union_subset ?_ ?_)
  · exact tsupport_mul_subset_right
  · exact tsupport_mul_subset_right.trans (product_test_partial_support i j)

def h1AdjointTest (φ : h1Tests ι 2) (i : ι) (j : Fin 3) : h1Tests ι 1 :=
  ⟨h1CoordinateAdjoint φ.val i j, h1CoordinateAdjoint_contDiff φ i j,
    φ.prop.2.1.of_isClosed_subset (isClosed_tsupport _) (h1CoordinateAdjoint_support φ.val i j),
    (h1CoordinateAdjoint_support φ.val i j).trans φ.prop.2.2⟩

end
end ArtinMatthews.SourceHyperbolicGreen
