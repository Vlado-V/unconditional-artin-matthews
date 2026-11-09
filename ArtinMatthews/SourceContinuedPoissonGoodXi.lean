module

public import ArtinMatthews.SourceContinuedPoissonRowShifts
public import ArtinMatthews.VaryingKummerAnalyticGaussianFiniteContour


set_option backward.privateInPublic true
@[expose] public section

/-! The finite good-row ξ move for the literal source integrand. The two
horizontal pieces and the remaining right tail are retained in the exact
identity. Only the derived nonvanishing rectangle is used. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Set MeasureTheory
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "K" => sourceContinuedPoissonRowKernel F S₀ hζ η hJ
local notation "I" => sourceContinuedPoissonRowIntegral F S₀ hζ η hJ

theorem sourceContinuedPoissonRowXiSlice_integrable_right
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (a : ℝ) (ha : 1 < a) (w z : ℂ) (hw : 3/1000 ≤ w.re) (hz : 2/5 ≤ z.re) :
    Integrable (fun x : ℝ => K v u X Y Z (sourcePoissonVertical a x,w,z)) := by
  obtain ⟨C, _, hC⟩ := exists_sourceContinuedPoissonRowKernel_right_strip_bound F S₀ hζ η hJ hcut v u hu
    hX hY hZ a a w.re z.re ha
  let A := C*(sourceContourHeightWeight w.im*sourceContourHeightWeight z.im)
  have hg : Integrable (fun x : ℝ => Real.exp (-((x+z.im)^2))) := by
    have h : Integrable (fun y : ℝ => Real.exp (-(y^2))) := by
      simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
    simpa only [add_comm] using h.comp_add_left z.im
  have hc : Continuous (fun x : ℝ => K v u X Y Z (sourcePoissonVertical a x,w,z)) := by
    apply (sourceContinuedPoissonRowKernel_continuousOn F S₀ hζ η hJ v u hcut hu hX hY hZ).comp_continuous
      ((sourcePoissonVertical_continuous a).prodMk continuous_const)
    intro x
    refine ⟨sourceRowEulerOpenDomain_low_w_right F S₀ hζ η hJ u.val u.property
      (sourcePoissonVertical a x,w,z) (by simpa only [sourcePoissonVertical_re] using ha) hw hz, ?_⟩
    change 0 < z.re
    linarith
  apply (hg.const_mul A).mono' hc.aestronglyMeasurable
  filter_upwards with x
  have h := hC a ⟨le_rfl,le_rfl⟩ w.re ⟨hw,le_rfl⟩ z.re ⟨hz,le_rfl⟩ w.im z.im x
  simpa only [A, sourcePoissonVertical, Complex.re_add_im] using h

theorem sourceContinuedPoissonRowKernel_finite_good_xi
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F)
    {ι : Type} [Fintype ι] (f : ι → {a : R // a ≠ 0}) (i : ι)
    (hu : ¬ ∃ x : F, x^6 = ((f i).val : F))
    (U r : ℝ) (hU : 0 ≤ U) (hr : 0 ≤ r)
    (hi : i ∉ sourceRowTwistDyadicExcludedRows F S₀ hζ η hJ f U r)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (w z : ℂ) (hw : 3/1000 ≤ w.re) (hz : 2/5 ≤ z.re) :
    let L := fun ξ : ℂ => K v (f i) X Y Z (ξ,w,z)
    (∫ x : ℝ, L (sourcePoissonVertical principalProbeSigma x)) =
      finiteVerticalIntegral L (499/500) (U^r) +
        finiteHorizontalError L (499/500) principalProbeSigma (U^r) +
        rightVerticalTail L principalProbeSigma (U^r) := by
  let L := fun ξ : ℂ => K v (f i) X Y Z (ξ,w,z)
  have hT : 0 ≤ U^r := Real.rpow_nonneg hU r
  have hσ : 1 < principalProbeSigma := by norm_num [principalProbeSigma]
  have hd : DifferentiableOn ℂ L
      {ξ : ℂ | (499/500 : ℝ) ≤ ξ.re ∧ ξ.re ≤ principalProbeSigma ∧ |ξ.im| ≤ U^r} := by
    apply sourceContinuedPoissonRowKernel_differentiableOn_path F S₀ hζ η hJ hcut v (f i) hu hX hY hZ
      (p := fun ξ => (ξ,w,z)) (by fun_prop)
    · intro ξ hξ
      exact sourceRowEulerOpenDomain_low_w_good F S₀ hζ η hJ f U r hU hr i hi (ξ,w,z)
        hξ.1 hw hz (hξ.2.2.trans (by linarith))
    · intro _ _
      change 0 < z.re
      linarith
  exact full_vertical_finite_shift L (by norm_num [principalProbeSigma]) hT hd
    (sourceContinuedPoissonRowXiSlice_integrable_right F S₀ hζ η hJ hcut v (f i) hu hX hY hZ
      principalProbeSigma hσ w z hw hz)

theorem sourceContinuedPoissonRowIntegral_finite_good_xi
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F)
    {ι : Type} [Fintype ι] (f : ι → {a : R // a ≠ 0}) (i : ι)
    (hu : ¬ ∃ x : F, x^6 = ((f i).val : F))
    (U r : ℝ) (hU : 0 ≤ U) (hr : 0 ≤ r)
    (hi : i ∉ sourceRowTwistDyadicExcludedRows F S₀ hζ η hJ f U r)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    I v (f i) X Y Z 4 4 2 = (1/(2*Real.pi) : ℂ)^3 *
      ∫ wt : ℝ × ℝ,
        let L := fun ξ : ℂ => K v (f i) X Y Z
          (ξ,sourcePoissonVertical (3/1000) wt.1,sourcePoissonVertical (2/5) wt.2)
        finiteVerticalIntegral L (499/500) (U^r) +
          finiteHorizontalError L (499/500) principalProbeSigma (U^r) +
          rightVerticalTail L principalProbeSigma (U^r) := by
  have hσ : 1 < principalProbeSigma := by norm_num [principalProbeSigma]
  rw [sourceContinuedPoissonRowIntegral_low_w F S₀ hζ η hJ hcut v (f i) hu hX hY hZ]
  unfold sourceContinuedPoissonRowIntegral
  apply congrArg ((1/(2*Real.pi) : ℂ)^3 * ·)
  rw [sourcePoissonHeight_integral_xi_inside _
    (sourceContinuedPoissonRowOnLines_integrable_right F S₀ hζ η hJ v (f i) hcut hu hX hY hZ
      principalProbeSigma (3/1000) (2/5) hσ le_rfl le_rfl)]
  apply integral_congr_ae
  filter_upwards with wt
  exact sourceContinuedPoissonRowKernel_finite_good_xi F S₀ hζ η hJ hcut v f i hu U r hU hr hi hX hY hZ
    (sourcePoissonVertical (3/1000) wt.1) (sourcePoissonVertical (2/5) wt.2) (by norm_num) (by norm_num)

end
end ArtinMatthews.SourceEulerAssembly
