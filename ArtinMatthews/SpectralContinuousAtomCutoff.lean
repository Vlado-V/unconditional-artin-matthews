module

public import ArtinMatthews.SpectralContinuousQuadraticMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import ArtinMatthews.SpectralLp2DominatedLimit


set_option backward.privateInPublic true
@[expose] public section

/-! Continuous bounded rational cutoffs converge to the literal
single-energy indicator in the genuine scalar spectral L² space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace ArtinMatthews

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralQuadraticAtomSet (T : H →L[ℂ] H) (a : ℂ) : Set (spectrum ℂ T) :=
  {x | (x:ℂ)=a}

omit [CompleteSpace H] in
theorem spectralQuadraticAtomSet_measurable (T : H →L[ℂ] H) (a : ℂ) :
    MeasurableSet (spectralQuadraticAtomSet T a) :=
  measurableSet_eq_fun measurable_subtype_coe measurable_const

def spectralQuadraticAtomIndicator (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) (a : ℂ) :
    Lp ℂ 2 (spectralQuadraticMeasure T hT u) :=
  indicatorConstLp 2 (spectralQuadraticAtomSet_measurable T a) (measure_ne_top _ _) 1

theorem spectralQuadraticAtomIndicator_ae (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) (a : ℂ) :
    spectralQuadraticAtomIndicator T hT u a =ᵐ[spectralQuadraticMeasure T hT u]
      (spectralQuadraticAtomSet T a).indicator (fun _ => (1:ℂ)) :=
  indicatorConstLp_coeFn

def spectralQuadraticAtomBump (T : H →L[ℂ] H) (a : ℂ) (n : ℕ) : C(spectrum ℂ T,ℂ) :=
  ⟨fun x => (((1+(n:ℝ)*‖(x:ℂ)-a‖^2)⁻¹:ℝ):ℂ),
    Complex.continuous_ofReal.comp ((show Continuous (fun x : spectrum ℂ T =>
      1+(n:ℝ)*‖(x:ℂ)-a‖^2) from
        continuous_const.add (continuous_const.mul ((continuous_subtype_val.sub continuous_const).norm.pow 2))).inv₀
      (fun x => ne_of_gt (by positivity)))⟩

omit [CompleteSpace H] in
theorem spectralQuadraticAtomBump_norm_le (T : H →L[ℂ] H) (a : ℂ) (n : ℕ) (x : spectrum ℂ T) :
    ‖spectralQuadraticAtomBump T a n x‖≤1 := by
  let d : ℝ := 1+(n:ℝ)*‖(x:ℂ)-a‖^2
  have hd : 0<d := by dsimp [d];positivity
  have hd1 : 1≤d := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  change ‖((d⁻¹:ℝ):ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hd.le),← one_div]
  exact (div_le_iff₀ hd).mpr (by simpa only [one_mul] using hd1)

omit [CompleteSpace H] in
theorem spectralQuadraticAtomBump_tendsto_pointwise (T : H →L[ℂ] H) (a : ℂ) (x : spectrum ℂ T) :
    Tendsto (fun n => spectralQuadraticAtomBump T a n x) atTop
      (𝓝 ((spectralQuadraticAtomSet T a).indicator (fun _ => (1:ℂ)) x)) := by
  by_cases hx : (x:ℂ)=a
  · have hm : x∈spectralQuadraticAtomSet T a := hx
    rw [Set.indicator_of_mem hm]
    simpa only [spectralQuadraticAtomBump,ContinuousMap.coe_mk,hx,sub_self,norm_zero,
      zero_pow (by decide : (2:ℕ)≠0),mul_zero,add_zero,inv_one,Complex.ofReal_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1))
  · have hn : x∉spectralQuadraticAtomSet T a := hx
    rw [Set.indicator_of_notMem hn]
    have hd : 0<‖(x:ℂ)-a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx))
    have h := (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const hd
    have h' := tendsto_atTop_add_const_left atTop (1:ℝ) h
    have hi := tendsto_inv_atTop_zero.comp h'
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hi
    simpa only [Function.comp_def,Complex.ofReal_zero,spectralQuadraticAtomBump,ContinuousMap.coe_mk] using hc

theorem spectralQuadraticAtomBump_tendsto_Lp (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) (a : ℂ) :
    Tendsto (fun n => ContinuousMap.toLp 2 (spectralQuadraticMeasure T hT u) ℂ
      (spectralQuadraticAtomBump T a n)) atTop (𝓝 (spectralQuadraticAtomIndicator T hT u a)) := by
  let μ := spectralQuadraticMeasure T hT u
  let G := (spectralQuadraticAtomSet T a).indicator (fun _ => (1:ℂ))
  refine spectralLp2_tendsto_of_domination _ _ (fun n => spectralQuadraticAtomBump T a n) G
    (fun n => ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) μ _) (spectralQuadraticAtomIndicator_ae T hT u a)
    (Eventually.of_forall (spectralQuadraticAtomBump_tendsto_pointwise T a))
    (fun _ => (2:ℝ)^2) (integrable_const _) (fun n => Eventually.of_forall fun x => ?_)
  have hg : ‖G x‖≤1 := by
    by_cases hx : x∈spectralQuadraticAtomSet T a
    · simp [G,Set.indicator_of_mem hx]
    · simp [G,Set.indicator_of_notMem hx]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤2)).mpr
  exact (norm_sub_le _ _).trans (by linarith [spectralQuadraticAtomBump_norm_le T a n x])

end ArtinMatthews
