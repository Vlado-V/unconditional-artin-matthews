module

public import ArtinMatthews.SpectralContinuousAtomCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! A scalar spectral atom yields an actual Hilbert-space eigenvector,
with the measure of the atom equal to its squared norm. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace ArtinMatthews

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralQuadraticAtomVector (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) (a : ℂ) : H :=
  spectralQuadraticCyclicMap T hT u (spectralQuadraticAtomIndicator T hT u a)

theorem spectralQuadraticAtomVector_tendsto (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) (a : ℂ) :
    Tendsto (fun n => (cfcHom hT (spectralQuadraticAtomBump T a n)) u) atTop
      (𝓝 (spectralQuadraticAtomVector T hT u a)) := by
  have h := (spectralQuadraticCyclicMap T hT u).continuous.continuousAt.tendsto.comp
    (spectralQuadraticAtomBump_tendsto_Lp T hT u a)
  apply h.congr
  intro n
  exact spectralQuadraticCyclicMap_toLp T hT u (spectralQuadraticAtomBump T a n)

def spectralQuadraticShiftSymbol (T : H →L[ℂ] H) (a : ℂ) : C(spectrum ℂ T,ℂ) :=
  (ContinuousMap.id ℂ).restrict (spectrum ℂ T)-a • (1:C(spectrum ℂ T,ℂ))

omit [CompleteSpace H] in
theorem spectralQuadraticShiftSymbol_apply (T : H →L[ℂ] H) (a : ℂ) (x : spectrum ℂ T) :
    spectralQuadraticShiftSymbol T a x=(x:ℂ)-a := by
  simp [spectralQuadraticShiftSymbol]

theorem spectralQuadraticShiftSymbol_cfc (T : H →L[ℂ] H) (hT : IsStarNormal T) (a : ℂ) :
    cfcHom hT (spectralQuadraticShiftSymbol T a)=T-a • (1:H →L[ℂ] H) := by
  rw [spectralQuadraticShiftSymbol,map_sub,map_smul,map_one,cfcHom_id]

theorem spectralQuadraticAtomVector_eigen (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) (a : ℂ) :
    T (spectralQuadraticAtomVector T hT u a)=a • spectralQuadraticAtomVector T hT u a := by
  let μ := spectralQuadraticMeasure T hT u
  let p := spectralQuadraticAtomBump T a
  let A : H →L[ℂ] H := T-a • 1
  let d := spectralQuadraticShiftSymbol T a
  let v := spectralQuadraticAtomVector T hT u a
  have hEq (n : ℕ) : ‖A ((cfcHom hT (p n)) u)‖^2=∫ x,‖d x*p n x‖^2 ∂μ := by
    have hp := (spectralQuadraticMeasure_integral_norm_sq T hT u (d*p n)).symm
    rw [map_mul,spectralQuadraticShiftSymbol_cfc,mul_apply_eq_comp] at hp
    exact hp
  have hInt : Tendsto (fun n : ℕ => ∫ x,‖d x*p n x‖^2 ∂μ) atTop
      (𝓝 (∫ _ : spectrum ℂ T,(0:ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖d x‖^2)
    · exact Eventually.of_forall fun n => ((d.continuous.mul (p n).continuous).norm.pow 2).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _),norm_mul]
        apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mpr
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (spectralQuadraticAtomBump_norm_le T a n x) (norm_nonneg (d x))
    · exact (d.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact Eventually.of_forall fun x => by
        have h := ((spectralQuadraticAtomBump_tendsto_pointwise T a x).const_mul (d x)).norm.pow 2
        by_cases hx : (x:ℂ)=a
        · have hd : d x=0 := (spectralQuadraticShiftSymbol_apply T a x).trans (sub_eq_zero.mpr hx)
          simpa only [p,hd,zero_mul,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using h
        · have hn : x∉spectralQuadraticAtomSet T a := hx
          simpa only [p,Set.indicator_of_notMem hn,mul_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using h
  rw [integral_zero] at hInt
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (hInt.congr fun n => (hEq n).symm)
  have hn : Tendsto (fun n => ‖A ((cfcHom hT (p n)) u)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs
  have hz : Tendsto (fun n => A ((cfcHom hT (p n)) u)) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hn)
  have hv : Tendsto (fun n => A ((cfcHom hT (p n)) u)) atTop (𝓝 (A v)) :=
    A.continuous.continuousAt.tendsto.comp (spectralQuadraticAtomVector_tendsto T hT u a)
  exact sub_eq_zero.mp (tendsto_nhds_unique hv hz)

theorem spectralQuadraticAtomVector_norm_sq (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) (a : ℂ) :
    ‖spectralQuadraticAtomVector T hT u a‖^2 =
      (spectralQuadraticMeasure T hT u).real (spectralQuadraticAtomSet T a) := by
  let μ := spectralQuadraticMeasure T hT u
  let S := spectralQuadraticAtomSet T a
  let e := spectralQuadraticAtomIndicator T hT u a
  change ‖spectralQuadraticCyclicMap T hT u e‖^2=μ.real S
  rw [LinearIsometry.norm_map,spectralLp2_norm_sq_integral]
  have h : (fun x => ‖e x‖^2) =ᵐ[μ] S.indicator (fun _ => (1:ℝ)) := by
    filter_upwards [spectralQuadraticAtomIndicator_ae T hT u a] with x hx
    change ‖e x‖^2=S.indicator (fun _ => (1:ℝ)) x
    have hE : e x=S.indicator (fun _ => (1:ℂ)) x := hx
    rw [hE]
    by_cases hm : x∈S
    · simp [Set.indicator_of_mem hm]
    · simp [Set.indicator_of_notMem hm]
  rw [integral_congr_ae h,integral_indicator (spectralQuadraticAtomSet_measurable T a),integral_const,
    smul_eq_mul,mul_one,MeasureTheory.measureReal_restrict_apply_univ]

theorem spectralQuadraticMeasure_atom (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) (a : ℂ) :
    spectralQuadraticMeasure T hT u (spectralQuadraticAtomSet T a)=
      ENNReal.ofReal (‖spectralQuadraticAtomVector T hT u a‖^2) := by
  rw [spectralQuadraticAtomVector_norm_sq]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

end ArtinMatthews
