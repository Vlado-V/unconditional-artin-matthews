module

public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SchwartzGradient
public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential
public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalSmoothRegularity


set_option backward.privateInPublic true
@[expose] public section

/-! The physical Euclidean weak equation transfers to the normalized
Fourier gradient with the exact factor (\lVert 2\pi i\rVert^2). -/

namespace ArtinMatthews

open MeasureTheory Set Filter
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
open scoped SchwartzMap ContDiff Topology ComplexConjugate

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

local notation "J" => SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
local notation "grad" => EuclideanGradient.CM.Construction.sobolevVectorGradient
local notation "ordinary" => SchwartzGradient.CM.Construction.schwartzOrdinaryGradient
local notation "coord" => SobolevIs.CM.Construction.schwartzSobolevCoordinate 1
local notation "mulL2" => CutoffDifferential.CM.Construction.schwartzL2Multiply
local notation "cF" => (2 * Real.pi * Complex.I : ℂ)
local notation "sF" => (‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2)

private theorem fourierScale_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

theorem sourceRealInner_complex_smul_both (z : ℂ) (a b : EuclideanSpace ℂ ι) :
    inner ℝ (z • a) (z • b) = ‖z‖^2 * inner ℝ a b := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (z • a i) (z • b i) = ‖z‖^2 * inner ℝ (a i) (b i)
  simp only [Complex.inner,smul_eq_mul,map_mul]
  rw [show z * b i * (conj z * conj (a i)) =
    ((‖z‖^2 : ℝ) : ℂ) * (b i * conj (a i)) by rw [Complex.ofReal_pow,← Complex.mul_conj']; ring]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem sourceOrdinaryEnergy_eq_fourierScale (b : OrthonormalBasis ι ℝ E)
    (A₀ A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) {U : Set E}
    (hAeq : EqOn A A₀ U)
    (hcomm : ∀ x ∈ U, ∀ w : EuclideanSpace ℂ ι, A₀ x (cF • w) = cF • A₀ x w)
    (u : Lp ℂ 2 (volume : Measure E))
    (G : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E)) (hG : cF • grad b u = G)
    (g : 𝓢(E, ℂ)) (hgU : tsupport g ⊆ U) :
    (∫ x, inner ℝ (A₀ x (G x)) (ordinary b g x)) =
      sF * ∫ x, inner ℝ (A x (grad b u x)) (grad b (coord g) x) := by
  have hu : ∀ᵐ x ∂(volume : Measure E), cF • grad b u x = G x := by
    filter_upwards [Lp.coeFn_smul cF (grad b u)] with x hx
    rw [hG] at hx
    exact hx.symm
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hu,SchwartzGradient.CM.Construction.sobolevVectorGradient_schwartz_normalization b g]
    with x hux htest
  by_cases hx : x ∈ tsupport g
  · rw [← hux,← htest,hAeq (hgU hx),hcomm x (hgU hx)]
    exact sourceRealInner_complex_smul_both cF _ _
  · have hzero := SchwartzGradient.CM.Construction.schwartzOrdinaryGradient_zero b g hx
    have hnormzero : grad b (coord g) x = 0 :=
      (smul_eq_zero.mp (htest.trans hzero)).resolve_left fourierScale_ne_zero
    rw [hzero,hnormzero,inner_zero_right,inner_zero_right,mul_zero]

omit [Fintype ι] in
theorem sourceEigenForcing_eq_fourierScale {U : Set E} (d : E → ℂ)
    (u M : Lp ℂ 2 (volume : Measure E)) (hM : J u = M)
    (m : 𝓢(E, ℂ)) (hm : EqOn m (fun x => ((sF : ℝ) : ℂ)⁻¹ * d x) U)
    (g : 𝓢(E, ℂ)) (hgU : tsupport g ⊆ U) :
    (∫ x, inner ℝ (d x • M x) (g x)) = sF * inner ℝ (mulL2 m (J u)) (g.toLp 2) := by
  change _ = sF * ∫ x, inner ℝ (mulL2 m (J u) x) (g.toLp 2 (volume : Measure E) x)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [CutoffDifferential.CM.Construction.schwartzL2Multiply_coe m (J u),
    g.coeFn_toLp 2 (volume : Measure E)] with x hmul hg
  rw [hmul,hg,hM]
  by_cases hx : g x = 0
  · rw [hx,inner_zero_right,inner_zero_right,mul_zero]
  · have hm' : ((sF : ℝ) : ℂ) * m x = d x := by
      rw [hm (hgU ((subset_tsupport g) hx)),mul_inv_cancel_left₀]
      exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr fourierScale_ne_zero))
    calc
      _ = inner ℝ ((sF : ℝ) • (m x • M x)) (g x) := by
        congr 1
        change d x * M x = ((sF : ℝ) : ℂ) * (m x * M x)
        rw [← mul_assoc,hm']
      _ = _ := real_inner_smul_left _ _ _

theorem sourceLocalEigen_of_native_tests (b : OrthonormalBasis ι ℝ E)
    (A₀ A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) {U : Set E}
    (hA : Continuous A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (hAeq : EqOn A A₀ U)
    (hcomm : ∀ x ∈ U, ∀ w : EuclideanSpace ℂ ι, A₀ x (cF • w) = cF • A₀ x w)
    (u M : Lp ℂ 2 (volume : Measure E)) (G : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hM : J u = M) (hG : cF • grad b u = G)
    (d : E → ℂ) (m : 𝓢(E, ℂ)) (hm : EqOn m (fun x => ((sF : ℝ) : ℂ)⁻¹ * d x) U)
    (hsol : ∀ g : 𝓢(E, ℂ), HasCompactSupport (g : E → ℂ) → tsupport g ⊆ U →
      (∫ x, inner ℝ (A₀ x (G x)) (ordinary b g x)) = ∫ x, inner ℝ (d x • M x) (g x)) :
    LocalSmoothRegularity.CM.Construction.IsLocalEuclideanWeakMetricSolution b A U u (mulL2 m (J u)) := by
  apply LocalSmoothRegularity.CM.Construction.localWeakMetricSolution_of_schwartz_tests b A
    hA.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  intro g hgc hgU
  apply mul_left_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr fourierScale_ne_zero))
  exact (sourceOrdinaryEnergy_eq_fourierScale b A₀ A hAeq hcomm u G hG g hgU).symm.trans
    ((hsol g hgc hgU).trans (sourceEigenForcing_eq_fourierScale d u M hM m hm g hgU))

end
end ArtinMatthews
