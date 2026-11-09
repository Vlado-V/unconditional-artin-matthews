module

public import ArtinMatthews.SourceKPFiniteChartL2Lift
public import ArtinMatthews.SourceKPArchActionSmooth
public import ArtinMatthews.SourceHyperbolicC1Green


set_option backward.privateInPublic true
@[expose] public section

/-! Literal compact scalar tests on the center-retaining automorphic quotient. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPCompactChartPullback (f : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (b : SourceKPFiniteLevelFiber K hζ) (x : ProductSpace (InfinitePlace K)) : ℂ :=
  if x ∈ productUpper (InfinitePlace K) then
    f (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x)) else 0

theorem sourceKPCompactChartPullback_add (f g : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPCompactChartPullback K hζ (f+g) b =
      sourceKPCompactChartPullback K hζ f b + sourceKPCompactChartPullback K hζ g b := by
  funext x
  by_cases hx : x ∈ productUpper (InfinitePlace K) <;>
    simp only [sourceKPCompactChartPullback,hx,ite_true,ite_false,Pi.add_apply,add_zero]

theorem sourceKPCompactChartPullback_smul (c : ℂ) (f : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPCompactChartPullback K hζ (c • f) b = c • sourceKPCompactChartPullback K hζ f b := by
  funext x
  by_cases hx : x ∈ productUpper (InfinitePlace K) <;>
    simp only [sourceKPCompactChartPullback,hx,ite_true,ite_false,Pi.smul_apply,smul_zero]

def sourceKPCompactCore (n : ℕ∞ω) : Submodule ℂ (SourceKPAutomorphicCompactLevel K hζ → ℂ) where
  carrier := {f | Continuous f ∧ HasCompactSupport f ∧
    ∀ b, ContDiffOn ℝ n (sourceKPCompactChartPullback K hζ f b) (productUpper (InfinitePlace K))}
  zero_mem' := by
    refine ⟨continuous_const,HasCompactSupport.zero,?_⟩
    intro b
    have he : sourceKPCompactChartPullback K hζ 0 b = 0 := by
      funext x
      simp only [sourceKPCompactChartPullback,Pi.zero_apply,ite_self]
    rw [he]
    exact contDiffOn_const
  add_mem' := by
    rintro f g ⟨hf,hfc,hfd⟩ ⟨hg,hgc,hgd⟩
    refine ⟨hf.add hg,hfc.add hgc,?_⟩
    intro b
    rw [sourceKPCompactChartPullback_add]
    exact (hfd b).add (hgd b)
  smul_mem' := by
    rintro c f ⟨hf,hfc,hfd⟩
    refine ⟨hf.const_smul c,hfc.smul_left,?_⟩
    intro b
    rw [sourceKPCompactChartPullback_smul]
    exact (hfd b).const_smul c

abbrev sourceKPCompactC2Core := sourceKPCompactCore K hζ 2
abbrev sourceKPCompactC1Core := sourceKPCompactCore K hζ 1

def sourceKPCompactCoreWeaken {n m : ℕ∞ω} (hmn : m ≤ n) :
    sourceKPCompactCore K hζ n →ₗ[ℂ] sourceKPCompactCore K hζ m :=
  Submodule.inclusion fun _ hf => ⟨hf.1,hf.2.1,fun b => (hf.2.2 b).of_le hmn⟩

theorem sourceKPUpperToCompact_smul (b : SourceKPFiniteLevelFiber K hζ)
    (γ : sourceKPArchComponentSubgroup K hζ b) (x : SourceKPArchUpperHalfSpace K) :
    sourceKPUpperToCompact K hζ b (γ • x) = sourceKPUpperToCompact K hζ b x := by
  unfold sourceKPUpperToCompact
  apply congrArg (sourceKPArithmeticUpperComponentMap K hζ b)
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨γ,rfl⟩

theorem sourceKPCompactChartPullback_invariant (f : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (b : SourceKPFiniteLevelFiber K hζ) (γ : sourceKPArchComponentSubgroup K hζ b)
    (x : ProductSpace (InfinitePlace K)) (hx : x ∈ productUpper (InfinitePlace K)) :
    sourceKPCompactChartPullback K hζ f b (sourceKPArchEuclideanAction K hζ γ.val x) =
      sourceKPCompactChartPullback K hζ f b x := by
  rw [sourceKPCompactChartPullback,ite_eq_left (sourceKPArchEuclideanAction_positive K hζ γ.val x),
    sourceKPCompactChartPullback,ite_eq_left hx]
  apply congrArg f
  unfold sourceKPArchEuclideanAction
  rw [sourceKPArchUpperEuclideanMap_left_inverse]
  exact sourceKPUpperToCompact_smul K hζ b γ (sourceKPArchEuclideanUpperMap K x)

def sourceKPCompactCoreGradientLift {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n)
    (b : SourceKPFiniteLevelFiber K hζ) (x : ProductSpace (InfinitePlace K)) :
    H1Vector (InfinitePlace K) :=
  WithLp.toLp 2 (fun ij : InfinitePlace K × Fin 3 =>
    (x ij.1 2 : ℂ) * productPartial (sourceKPCompactChartPullback K hζ f.val b) ij.1 ij.2 x)

def sourceKPCompactCoreEnergyLift {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n)
    (b : SourceKPFiniteLevelFiber K hζ) (x : ProductSpace (InfinitePlace K)) : ℝ :=
  productGradientEnergy (sourceKPCompactChartPullback K hζ f.val b) x

theorem sourceKPCompactCoreEnergyLift_nonneg {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n)
    (b : SourceKPFiniteLevelFiber K hζ) (x : ProductSpace (InfinitePlace K)) :
    0 ≤ sourceKPCompactCoreEnergyLift K hζ f b x := by
  unfold sourceKPCompactCoreEnergyLift productGradientEnergy
  positivity

end
end ArtinMatthews
