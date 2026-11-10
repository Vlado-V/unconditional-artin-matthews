module

public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! Literal bounded continuous multiplication on L², including its
integrable weighted pairing and operator identities. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace BoundedContinuousFunction
namespace ArtinMatthews

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)

theorem spectralLpTest_memLp (m : X →ᵇ ℂ) (f : Lp ℂ 2 μ) :
    MemLp (fun x => m x*f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c:=‖m‖)
    (m.continuous.measurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact ae_of_all _ (fun x => by
    change ‖m x*f x‖≤‖m‖*‖f x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm x) (norm_nonneg _))

def spectralLpTestValue (m : X →ᵇ ℂ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (spectralLpTest_memLp μ m f).toLp _

theorem spectralLpTestValue_ae (m : X →ᵇ ℂ) (f : Lp ℂ 2 μ) :
    spectralLpTestValue μ m f=ᵐ[μ] fun x => m x*f x :=
  (spectralLpTest_memLp μ m f).coeFn_toLp

theorem spectralLpTestValue_norm (m : X →ᵇ ℂ) (f : Lp ℂ 2 μ) :
    ‖spectralLpTestValue μ m f‖≤‖m‖*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [spectralLpTestValue_ae μ m f] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm x) (norm_nonneg _)

def spectralLpTestMultiplier (m : X →ᵇ ℂ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := spectralLpTestValue μ m
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [spectralLpTestValue_ae μ m (f+g),spectralLpTestValue_ae μ m f,
          spectralLpTestValue_ae μ m g,Lp.coeFn_add f g,
          Lp.coeFn_add (spectralLpTestValue μ m f) (spectralLpTestValue μ m g)] with x hs hf hg hfg hv
        rw [hs,hv]
        simp only [Pi.add_apply]
        rw [hf,hg,hfg]
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro c f
        change spectralLpTestValue μ m (c • f)=c • spectralLpTestValue μ m f
        apply Lp.ext
        filter_upwards [spectralLpTestValue_ae μ m (c • f),spectralLpTestValue_ae μ m f,
          Lp.coeFn_smul c f,Lp.coeFn_smul c (spectralLpTestValue μ m f)] with x hs hf hcf hv
        rw [hs,hv]
        simp only [Pi.smul_apply,smul_eq_mul]
        rw [hf,hcf]
        simp only [Pi.smul_apply,smul_eq_mul]
        ring }
    ‖m‖ (fun f => by
      change ‖spectralLpTestValue μ m f‖≤‖m‖*‖f‖
      exact spectralLpTestValue_norm μ m f)

theorem spectralLpTestMultiplier_ae (m : X →ᵇ ℂ) (f : Lp ℂ 2 μ) :
    spectralLpTestMultiplier μ m f=ᵐ[μ] fun x => m x*f x := spectralLpTestValue_ae μ m f

theorem spectralLpTestMultiplier_inner (m : X →ᵇ ℂ) (f g : Lp ℂ 2 μ) :
    inner ℂ f (spectralLpTestMultiplier μ m g)=∫ x,m x*inner ℂ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectralLpTestMultiplier_ae μ m g] with x hx
  change inner ℂ (f x) ((spectralLpTestMultiplier μ m g) x)=_
  rw [hx,RCLike.inner_apply,RCLike.inner_apply]
  ring

theorem spectralLpTestMultiplier_integrable (m : X →ᵇ ℂ) (f g : Lp ℂ 2 μ) :
    Integrable (fun x => m x*inner ℂ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜:=ℂ) f (spectralLpTestMultiplier μ m g)).congr
  filter_upwards [spectralLpTestMultiplier_ae μ m g] with x hx
  change inner ℂ (f x) ((spectralLpTestMultiplier μ m g) x)=_
  rw [hx,RCLike.inner_apply,RCLike.inner_apply]
  ring

theorem spectralLpTestMultiplier_one : spectralLpTestMultiplier μ (1:X →ᵇ ℂ)=ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [spectralLpTestMultiplier_ae μ 1 f] with x hx
  simpa using hx

theorem spectralLpTestMultiplier_mul (m n : X →ᵇ ℂ) :
    (spectralLpTestMultiplier μ m).comp (spectralLpTestMultiplier μ n)=spectralLpTestMultiplier μ (m*n) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [spectralLpTestMultiplier_ae μ m (spectralLpTestMultiplier μ n f),
    spectralLpTestMultiplier_ae μ n f,spectralLpTestMultiplier_ae μ (m*n) f] with x hm hn hmn
  change (spectralLpTestMultiplier μ m (spectralLpTestMultiplier μ n f)) x=_
  rw [hm,hn,hmn]
  simp only [BoundedContinuousFunction.mul_apply]
  ring

end ArtinMatthews
