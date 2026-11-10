module

public import ArtinMatthews.SourceHyperbolicProductMeasure
public import OAI.NumberTheory.DirichletL.CubicSieve.RadialProfiles
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def productDirection (i : ι) (j : Fin 3) : ProductSpace ι :=
  Pi.single i (euclideanCoordinateVector j)

def productHeightCLM (i : ι) : ProductSpace ι →L[ℝ] ℂ :=
  euclideanHeightCLM.comp (ContinuousLinearMap.proj i)

omit [Fintype ι] in
theorem productHeightCLM_apply (i : ι) (p : ProductSpace ι) :
    productHeightCLM i p = (p i 2 : ℂ) := rfl

def productPartial (f : ProductSpace ι → ℂ) (i : ι) (j : Fin 3) (p : ProductSpace ι) : ℂ :=
  fderiv ℝ f p (productDirection i j)

def otherWeight (i : ι) (p : ProductSpace ι) : ℂ :=
  ∏ k ∈ (Finset.univ.erase i), ((p k 2 : ℂ)^3)⁻¹

def productWeightedPartial (f : ProductSpace ι → ℂ) (i : ι) (j : Fin 3)
    (p : ProductSpace ι) : ℂ :=
  otherWeight i p * productPartial f i j p / (p i 2 : ℂ)

omit [Fintype ι] in
theorem productUpper_pos {p : ProductSpace ι} (hp : p ∈ productUpper ι) (i : ι) :
    0 < p i 2 := hp i (Set.mem_univ i)

theorem productPartial_contDiffAt {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 2 f p) (i : ι) (j : Fin 3) :
    ContDiffAt ℝ 1 (productPartial f i j) p :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

theorem otherWeight_contDiffAt {p : ProductSpace ι} (hp : p ∈ productUpper ι) (i : ι) :
    ContDiffAt ℝ 1 (otherWeight i) p := by
  apply contDiffAt_prod
  intro k _
  have hH : ContDiffAt ℝ 1 (fun q : ProductSpace ι => (q k 2 : ℂ)) p :=
    (productHeightCLM k).contDiff.contDiffAt
  exact (hH.pow 3).fun_inv (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (productUpper_pos hp k).ne'))

theorem productWeightedPartial_contDiffAt {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 2 f p) (hp : p ∈ productUpper ι) (i : ι) (j : Fin 3) :
    ContDiffAt ℝ 1 (productWeightedPartial f i j) p := by
  have hH : ContDiffAt ℝ 1 (fun q : ProductSpace ι => (q i 2 : ℂ)) p :=
    (productHeightCLM i).contDiff.contDiffAt
  simpa only [productWeightedPartial, div_eq_mul_inv] using!
    ((otherWeight_contDiffAt hp i).mul (productPartial_contDiffAt hf i j)).mul
      (hH.fun_inv (Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne'))

theorem otherWeight_on_line (p : ProductSpace ι) (i : ι) (j : Fin 3) (t : ℝ) :
    otherWeight i (p+t • productDirection i j) = otherWeight i p := by
  apply Finset.prod_congr rfl
  intro k hk
  have hki : k ≠ i := (Finset.mem_erase.mp hk).1
  have he : (p+t • productDirection i j) k = p k := by
    change p k+t • ((Pi.single i (euclideanCoordinateVector j) : ProductSpace ι) k) = p k
    rw [Pi.single_eq_of_ne hki, smul_zero, add_zero]
  rw [he]

theorem productWeightedPartial_derivative {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 2 f p) (hp : p ∈ productUpper ι) (i : ι) (j : Fin 3) :
    productPartial (productWeightedPartial f i j) i j p =
      otherWeight i p *
        (productPartial (productPartial f i j) i j p * (p i 2 : ℂ) -
          productPartial f i j p * (euclideanCoordinateVector j 2 : ℂ)) / (p i 2 : ℂ)^2 := by
  have hF := ((productPartial_contDiffAt hf i j).differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt
    (productDirection i j)
  have hH := ((productHeightCLM i).hasFDerivAt (x := p)).hasLineDerivAt (productDirection i j)
  change HasDerivAt (fun t : ℝ => productPartial f i j (p+t • productDirection i j))
    (productPartial (productPartial f i j) i j p) 0 at hF
  change HasDerivAt (fun t : ℝ => productHeightCLM i (p+t • productDirection i j))
    (productHeightCLM i (productDirection i j)) 0 at hH
  have hn : productHeightCLM i (p+(0 : ℝ) • productDirection i j) ≠ 0 := by
    simpa only [zero_smul, add_zero, productHeightCLM_apply] using
      (Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne')
  have h := (hF.div hH hn).const_mul (otherWeight i p)
  have hline : HasLineDerivAt ℝ (productWeightedPartial f i j)
      (otherWeight i p *
        (productPartial (productPartial f i j) i j p * (p i 2 : ℂ) -
          productPartial f i j p * (euclideanCoordinateVector j 2 : ℂ)) / (p i 2 : ℂ)^2)
      p (productDirection i j) := by
    simp only [HasLineDerivAt, productWeightedPartial]
    simp_rw [otherWeight_on_line]
    simpa only [Pi.div_apply, zero_smul, add_zero, productHeightCLM_apply,
      productDirection, Pi.single_eq_same, mul_div_assoc] using! h
  exact (((productWeightedPartial_contDiffAt hf hp i j).differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt
    (productDirection i j)).unique hline

end
end ArtinMatthews.SourceHyperbolicGreen
