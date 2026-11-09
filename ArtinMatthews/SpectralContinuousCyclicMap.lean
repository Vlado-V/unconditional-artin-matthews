module

public import ArtinMatthews.SpectralContinuousQuadraticIntegral
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! The actual functional-calculus state extends isometrically from
continuous functions to its entire scalar L² measure space. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace ArtinMatthews

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance spectralQuadraticMeasure_regular (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) :
    (spectralQuadraticMeasure T hT u).Regular := by
  unfold spectralQuadraticMeasure
  infer_instance

theorem spectralLp2_norm_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : ‖f‖^2=∫ x,‖f x‖^2 ∂μ := by
  have hi : Integrable (fun x : X => inner ℂ (f x) (f x)) μ :=
    memLp_one_iff_integrable.mp (L2.eLpNorm_inner_lt_top f f)
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),L2.inner_def,← integral_re hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (norm_sq_eq_re_inner (𝕜:=ℂ) (f x)).symm

def spectralQuadraticCyclicContinuous (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) :
    C(spectrum ℂ T,ℂ) →ₗ[ℂ] H where
  toFun f := (cfcHom hT f) u
  map_add' f g := by
    change (cfcHom hT (f+g)) u=(cfcHom hT f) u+(cfcHom hT g) u
    rw [map_add,add_apply]
  map_smul' a f := by
    change (cfcHom hT (a • f)) u=a • (cfcHom hT f) u
    rw [map_smul,smul_apply]

theorem spectralQuadraticCyclicContinuous_norm (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (u : H) (f : C(spectrum ℂ T,ℂ)) :
    ‖spectralQuadraticCyclicContinuous T hT u f‖=
      ‖ContinuousMap.toLp 2 (spectralQuadraticMeasure T hT u) ℂ f‖ := by
  let μ := spectralQuadraticMeasure T hT u
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(cfcHom hT f) u‖^2=‖ContinuousMap.toLp 2 μ ℂ f‖^2
  rw [← spectralQuadraticMeasure_integral_norm_sq T hT u f,spectralLp2_norm_sq_integral]
  apply integral_congr_ae
  exact (ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) μ f).symm.mono fun x hx => congrArg (fun z : ℂ => ‖z‖^2) hx

def spectralQuadraticCyclicMap (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) :
    Lp ℂ 2 (spectralQuadraticMeasure T hT u) →ₗᵢ[ℂ] H :=
  (spectralQuadraticCyclicContinuous T hT u).extendOfIsometry
    (e:=(ContinuousMap.toLp 2 (spectralQuadraticMeasure T hT u) ℂ).toLinearMap)
    (ContinuousMap.toLp_denseRange (p:=2) ℂ (spectralQuadraticMeasure T hT u) ℂ ENNReal.ofNat_ne_top)
    (spectralQuadraticCyclicContinuous_norm T hT u)

theorem spectralQuadraticCyclicMap_toLp (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H)
    (f : C(spectrum ℂ T,ℂ)) :
    spectralQuadraticCyclicMap T hT u (ContinuousMap.toLp 2 (spectralQuadraticMeasure T hT u) ℂ f)=
      (cfcHom hT f) u := by
  unfold spectralQuadraticCyclicMap
  exact LinearMap.extendOfIsometry_eq _ _ _ f

end ArtinMatthews
