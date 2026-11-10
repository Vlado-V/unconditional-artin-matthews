module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exponential of a bounded continuous function is an entire
Banach-valued family, and evaluation is the literal complex exponential. -/
noncomputable section
open scoped BoundedContinuousFunction
namespace ArtinMatthews
variable {X : Type*} [TopologicalSpace X]

def spectralBoundedEvalRingHom (x : X) : (X →ᵇ ℂ) →+* ℂ where
  toFun b := b x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def spectralBoundedExponential (b : X →ᵇ ℂ) (s : ℂ) : X →ᵇ ℂ :=
  NormedSpace.exp (s • b)

theorem spectralBoundedExponential_apply (b : X →ᵇ ℂ) (s : ℂ) (x : X) :
    spectralBoundedExponential b s x=Complex.exp (s*b x) := by
  have h := NormedSpace.map_exp (spectralBoundedEvalRingHom x)
    ((BoundedContinuousFunction.evalCLM ℂ x).continuous) (s • b)
  change spectralBoundedExponential b s x=NormedSpace.exp (s*b x) at h
  rw [← Complex.exp_eq_exp_ℂ] at h
  exact h

theorem spectralBoundedExponential_analyticAt (b : X →ᵇ ℂ) (s : ℂ) :
    AnalyticAt ℂ (spectralBoundedExponential b) s := by
  have h : AnalyticAt ℂ (fun w : ℂ => w • b) s := analyticAt_id.smul analyticAt_const
  exact (NormedSpace.exp_analytic (𝕂 := ℂ) (s • b)).comp (f := fun w : ℂ => w • b) h

end ArtinMatthews
