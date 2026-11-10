module

public import ArtinMatthews.SourceRetainedGeneratorBasis
public import ArtinMatthews.SourceRetainedFiniteInterpolation
public import Mathlib.Tactic.ContinuousFunctionalCalculus


set_option backward.privateInPublic true
@[expose] public section

/-! Finite tensor expansion of an arbitrary complex-valued function whose
partial slices respect the linear relations among the actual generators. -/
namespace ArtinMatthews

open scoped BigOperators

theorem sourceRetainedTensorExpansion
    {I : Type*} [Fintype I] [DecidableEq I]
    {G W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)]
    (v : ∀ i, G i → W i) (A : (∀ i, G i) → ℂ)
    (hrel : ∀ (g : ∀ i, G i) (i : I) (d : G i →₀ ℂ),
      d.sum (fun x z => z • v i x) = 0 →
        d.sum (fun x z => z * A (Function.update g i x)) = 0)
    (g : ∀ i, G i) :
    A g = ∑ k : (∀ i, Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range (v i))))),
      A (fun i => sourceRetainedBasisLift (v i) (k i)) *
        ∏ i, sourceRetainedCoordinate (v i) (k i) (v i (g i)) := by
  refine sourceRetainedFiniteInterpolation
    (fun i => sourceRetainedBasisLift (v i))
    (fun i k x => sourceRetainedCoordinate (v i) k (v i x)) A
    (fun i j k => sourceRetainedCoordinate_on_basisLift (v i) j k) ?_ g
  intro u i
  simpa only [Function.update_eq_self] using
    sourceRetainedSlice_expansion (v i) (fun x => A (Function.update u i x)) (hrel u i) (u i)

end ArtinMatthews
