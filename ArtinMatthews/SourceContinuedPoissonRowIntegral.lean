module

public import ArtinMatthews.SourceContinuedPoissonRowStripBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute integration of the continued row over the three literal
height lines. The measure uses the same height order and Gaussian shear
as the original source contour. -/
namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

theorem sourcePoissonHeightWeightProduct_integrable :
    Integrable (fun p : SourcePoissonHeights =>
      (sourceContourHeightWeight p.1.1*sourceContourHeightWeight p.1.2)*
        Real.exp (-((p.2+p.1.2)^2))) sourcePoissonHeightMeasure := by
  have hg : Integrable (fun r : ℝ => Real.exp (-(r^2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have h := (sourceContourHeightWeight_integrable.mul_prod sourceContourHeightWeight_integrable).mul_prod hg
  exact (sourceLogRadial_shear_measurePreserving ((volume : Measure ℝ).prod volume)
    (Prod.snd : ℝ × ℝ → ℝ) measurable_snd).integrable_comp_of_integrable h

end
end ArtinMatthews.SourcePhysical

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
def sourceContinuedPoissonRowOnLines (v : InfinitePlace F) (u : {a : R // a ≠ 0}) (X Y Z a b c : ℝ) (p : SourcePoissonHeights) : ℂ :=
  sourceContinuedPoissonRowKernel F S₀ hζ η hJ v u X Y Z
    (sourcePoissonVertical a p.2, sourcePoissonVertical b p.1.1, sourcePoissonVertical c p.1.2)

def sourceContinuedPoissonRowIntegral (v : InfinitePlace F) (u : {a : R // a ≠ 0}) (X Y Z a b c : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)^3 *
    ∫ p, sourceContinuedPoissonRowOnLines F S₀ hζ η hJ v u X Y Z a b c p ∂sourcePoissonHeightMeasure

theorem sourceContinuedPoissonRowKernel_continuousOn (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hcut : principalAngularCutoff F J ⊆ S) (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    ContinuousOn (sourceContinuedPoissonRowKernel F S₀ hζ η hJ v u X Y Z)
      (sourceRowEulerOpenDomain F hζ S₀ u.val u.property η hJ ∩ {p : ProbeCoordinates | 0 < p.2.2.re}) := by
  let D := sourceRowEulerOpenDomain F hζ S₀ u.val u.property η hJ ∩ {p : ProbeCoordinates | 0 < p.2.2.re}
  have hx : Continuous (fun p : ProbeCoordinates => (X : ℂ)^(1/2-p.2.2)) := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne')]
    fun_prop
  have hy : Continuous (fun p : ProbeCoordinates => (Y : ℂ)^(p.2.1-1)) := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne')]
    fun_prop
  have hz : Continuous (fun p : ProbeCoordinates => (Z : ℂ)^(p.1+p.2.2-1)) := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hZ.ne')]
    fun_prop
  have hg : Continuous (fun p : ProbeCoordinates => Complex.exp ((p.1+p.2.2-1)^2)) := by fun_prop
  have hq : Continuous (fun p : ProbeCoordinates => (sourcePoissonFrequencyNorm F S₀ u : ℂ)^(-p.2.2)) := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (sourcePoissonFrequencyNorm_pos F S₀ u).ne')]
    fun_prop
  have hM : ContinuousOn (fun p : ProbeCoordinates => sourceSLocalProbeMellin F hζ S v p.2.2) D :=
    (sourceSLocalProbeMellin_analyticOnNhd F hζ S v).continuousOn.comp continuous_snd.snd.continuousOn
      (fun _ hp => hp.2)
  have hW : Continuous (fun p : ProbeCoordinates => sourceProbeW1Mellin p.2.1) :=
    sourceProbeW1Mellin_entire.continuous.comp continuous_snd.fst
  have hF : ContinuousOn (sourceRowEulerContinuation F hζ S₀ u.val u.property η hJ) D :=
    ((sourceRowEulerContinuation_differentiableOn F hζ S₀ u.val u.property η hJ hcut hu).continuousOn).mono
      inter_subset_left
  exact ((((((hx.mul hz).mul hy).mul hg).continuousOn.mul hM).mul hW.continuousOn).mul (hq.continuousOn.mul hF))

theorem sourceContinuedPoissonRowOnLines_continuous_right (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hcut : principalAngularCutoff F J ⊆ S) (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (a b c : ℝ) (ha : 1 < a) (hb : 3/1000 ≤ b) (hc : 2/5 ≤ c) :
    Continuous (sourceContinuedPoissonRowOnLines F S₀ hζ η hJ v u X Y Z a b c) := by
  let p : SourcePoissonHeights → ProbeCoordinates := fun t =>
    (sourcePoissonVertical a t.2, sourcePoissonVertical b t.1.1, sourcePoissonVertical c t.1.2)
  have hp : Continuous p := ((sourcePoissonVertical_continuous a).comp continuous_snd).prodMk
    (((sourcePoissonVertical_continuous b).comp continuous_fst.fst).prodMk
      ((sourcePoissonVertical_continuous c).comp continuous_fst.snd))
  exact (sourceContinuedPoissonRowKernel_continuousOn F S₀ hζ η hJ v u hcut hu hX hY hZ).comp_continuous hp
    (fun t => ⟨sourceRowEulerOpenDomain_low_w_right F S₀ hζ η hJ u.val u.property (p t)
      (by simpa only [p, sourcePoissonVertical_re] using ha)
      (by simpa only [p, sourcePoissonVertical_re] using hb)
      (by simpa only [p, sourcePoissonVertical_re] using hc),
      by change 0 < (sourcePoissonVertical c t.1.2).re
         rw [sourcePoissonVertical_re]
         linarith⟩)

theorem sourceContinuedPoissonRowOnLines_integrable_right (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hcut : principalAngularCutoff F J ⊆ S) (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (a b c : ℝ) (ha : 1 < a) (hb : 3/1000 ≤ b) (hc : 2/5 ≤ c) :
    Integrable (sourceContinuedPoissonRowOnLines F S₀ hζ η hJ v u X Y Z a b c) sourcePoissonHeightMeasure := by
  obtain ⟨C, _, hC⟩ := exists_sourceContinuedPoissonRowKernel_right_strip_bound F S₀ hζ η hJ hcut v u hu
    hX hY hZ a a b c ha
  apply (sourcePoissonHeightWeightProduct_integrable.const_mul C).mono'
    (sourceContinuedPoissonRowOnLines_continuous_right F S₀ hζ η hJ v u hcut hu hX hY hZ
      a b c ha hb hc).aestronglyMeasurable
  filter_upwards with p
  exact (hC a ⟨le_rfl,le_rfl⟩ b ⟨hb,le_rfl⟩ c ⟨hc,le_rfl⟩ p.1.1 p.1.2 p.2).trans_eq (by ring)

end
end ArtinMatthews.SourceEulerAssembly
