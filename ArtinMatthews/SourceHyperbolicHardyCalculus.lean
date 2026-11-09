module

public import ArtinMatthews.SourceHyperbolicProductCalculus


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def productVertical (f : ProductSpace ι → ℂ) (i : ι) (p : ProductSpace ι) : ℂ :=
  (p i 2 : ℂ) * productPartial f i 2 p

def productRadial (f : ProductSpace ι → ℂ) (p : ProductSpace ι) : ℂ :=
  ∑ i, productVertical f i p

def productWeightedValue (f : ProductSpace ι → ℂ) (i : ι) (p : ProductSpace ι) : ℂ :=
  otherWeight i p * f p / (p i 2 : ℂ)^2

theorem productWeightedValue_contDiffAt {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 1 f p) (hp : p ∈ productUpper ι) (i : ι) :
    ContDiffAt ℝ 1 (productWeightedValue f i) p := by
  have hH : ContDiffAt ℝ 1 (fun q : ProductSpace ι => (q i 2 : ℂ)) p :=
    (productHeightCLM i).contDiff.contDiffAt
  simpa only [productWeightedValue, div_eq_mul_inv] using!
    ((otherWeight_contDiffAt hp i).mul hf).mul
      ((hH.pow 2).fun_inv (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne')))

theorem productWeightedValue_derivative {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 1 f p) (hp : p ∈ productUpper ι) (i : ι) :
    productPartial (productWeightedValue f i) i 2 p =
      otherWeight i p * ((p i 2 : ℂ) * productPartial f i 2 p - 2 * f p) /
        (p i 2 : ℂ)^3 := by
  have hF := (hf.differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt
    (productDirection i 2)
  have hH := ((productHeightCLM i).hasFDerivAt (x := p)).hasLineDerivAt (productDirection i 2)
  change HasDerivAt (fun t : ℝ => f (p+t • productDirection i 2))
    (productPartial f i 2 p) 0 at hF
  change HasDerivAt (fun t : ℝ => productHeightCLM i (p+t • productDirection i 2))
    (productHeightCLM i (productDirection i 2)) 0 at hH
  have hn : (productHeightCLM i (p+(0 : ℝ) • productDirection i 2))^2 ≠ 0 := by
    simpa only [zero_smul, add_zero, productHeightCLM_apply] using
      pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne')
  have h := (hF.div (hH.pow 2) hn).const_mul (otherWeight i p)
  have hline : HasLineDerivAt ℝ (productWeightedValue f i)
      (otherWeight i p * ((p i 2 : ℂ) * productPartial f i 2 p - 2 * f p) /
        (p i 2 : ℂ)^3) p (productDirection i 2) := by
    have hcalc : otherWeight i p *
        ((productPartial f i 2 p * (p i 2 : ℂ)^2 -
          f p * (2 * (p i 2 : ℂ) * (euclideanCoordinateVector 2 2 : ℂ))) /
            ((p i 2 : ℂ)^2)^2) =
        otherWeight i p * ((p i 2 : ℂ) * productPartial f i 2 p - 2 * f p) /
          (p i 2 : ℂ)^3 := by
      norm_num [euclideanCoordinateVector]
      field_simp [Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne']
    simp only [HasLineDerivAt, productWeightedValue]
    simp_rw [otherWeight_on_line]
    simpa only [Pi.div_apply, zero_smul, add_zero, productHeightCLM_apply,
      productDirection, Pi.single_eq_same, Pi.pow_apply, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, mul_div_assoc, hcalc] using! h
  exact (((productWeightedValue_contDiffAt hf hp i).differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt
    (productDirection i 2)).unique hline

theorem hardyPartial_continuous {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (i : ι) (j : Fin 3) : Continuous (productPartial f i j) :=
  ((hf.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous

theorem productWeightedValue_partial_continuousAt {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 1 f p) (hp : p ∈ productUpper ι) (i : ι) :
    ContinuousAt (productPartial (productWeightedValue f i) i 2) p :=
  (((productWeightedValue_contDiffAt hf hp i).fderiv_right (m := 0) (by norm_num)).clm_apply
    contDiffAt_const).continuousAt

end
end ArtinMatthews.SourceHyperbolicGreen
