module

public import ArtinMatthews.SourceKPAdelicOutgoingLocalCyclic
public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPResidualLocalFourierRelation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The residual Fourier coefficient descends to the actual local
exceptional cyclic representation at each finite place. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix StandardAdelic
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

private theorem finsupp_span_surjective {A E : Type*} [AddCommGroup E] [Module ℂ E]
    (C : Submodule ℂ E) (w : A → C)
    (hspan : ∀ f : C, f.val ∈ Submodule.span ℂ (Set.range fun g => (w g).val)) :
    Function.Surjective (Finsupp.linearCombination ℂ w) := by
  intro f
  obtain ⟨l,hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan f)
  refine ⟨l,Subtype.ext ?_⟩
  change C.subtype (Finsupp.linearCombination ℂ w l) = f.val
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,Submodule.subtype_apply]
  exact hl

private theorem finsupp_kernel_of_relations {A : Type} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (w : A → E) (a : A → ℂ)
    (hrel : ∀ {I : Type} [Fintype I] (g : I → A) (c : I → ℂ),
      (∑ i, c i • w (g i)) = 0 → (∑ i, c i * a (g i)) = 0) :
    LinearMap.ker (Finsupp.linearCombination ℂ w) ≤ LinearMap.ker (Finsupp.linearCombination ℂ a) := by
  classical
  intro l hl
  have hsum : (∑ i : l.support, l i.val • w i.val) = 0 := by
    rw [← Finset.sum_subtype l.support (fun _ => Iff.rfl) (fun g => l g • w g)]
    exact hl
  change (∑ g ∈ l.support, l g * a g) = 0
  rw [Finset.sum_subtype l.support (fun _ => Iff.rfl) (fun g => l g * a g)]
  exact hrel Subtype.val (fun i => l i.val) hsum

private def generatorLift {A E : Type*} [AddCommGroup E] [Module ℂ E]
    (w : A → E) (a : A → ℂ) (hq : Function.Surjective (Finsupp.linearCombination ℂ w))
    (hk : LinearMap.ker (Finsupp.linearCombination ℂ w) ≤
      LinearMap.ker (Finsupp.linearCombination ℂ a)) :
    {ℓ : E →ₗ[ℂ] ℂ // ∀ g, ℓ (w g) = a g} := by
  refine ⟨(Finsupp.linearCombination ℂ w).liftOfSurjective hq
    ⟨Finsupp.linearCombination ℂ a,hk⟩,?_⟩
  intro g
  have h := LinearMap.equivOfSurjective_apply hq hk (m := Finsupp.single g (1 : ℂ))
  simpa only [Finsupp.linearCombination_single,one_smul] using h

private theorem restricted_action_one {G E : Type*} [Monoid G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (C : Submodule ℂ E)
    (hC : ∀ (g : G) (v : E), v ∈ C → ρ g v ∈ C) (v : C) :
    (ρ 1).restrict (hC 1) v = v := by
  apply Subtype.ext
  change ρ 1 v.val = v.val
  rw [map_one,Module.End.one_apply]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hs : 0 < (1 / 6 : ℂ).re)

local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "S" => (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K)))
local notation "s₀" => (1 / 6 : ℂ)
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ S s₀ hs
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P s₀ hs
local notation "π₀" => sourceAlgebraicInducedRepresentation B₀ ρ₀
local notation "R₀" => sourceKPAdelicOutgoingRegularizedLocalSection K hζ P s₀ hs
local notation "C" => sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P s₀ hs
local notation "hC" => sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P s₀ hs
local notation "v₀" => sourceKPAdelicOutgoingRegularizedLocalCyclicVector K hζ P s₀ hs
local notation "r₀" => sourceKPJacquetRight K hζ P ρ₀ C hC
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "τ" => fun g : G => Prod.snd (ι₀ g)

local instance sourceKPResidualLocalFourierValueAddCommGroup : AddCommGroup W :=
  Submodule.addCommGroup _

private theorem localFourier_translate_val (g : G) : (r₀ g v₀).val = π₀ g (R₀).val := rfl

def sourceKPResidualLocalFourierGeneratorMap : (G →₀ ℂ) →ₗ[ℂ] C :=
  Finsupp.linearCombination ℂ (fun g : G => r₀ g v₀)

local notation "gen" => sourceKPResidualLocalFourierGeneratorMap K hζ P hs

theorem sourceKPResidualLocalFourierGenerators_surjective : Function.Surjective gen := by
  unfold sourceKPResidualLocalFourierGeneratorMap
  apply finsupp_span_surjective
  intro f
  simp only [localFourier_translate_val K hζ P hs]
  exact f.property

private def localResidualFourierValues {T : ℝ} (hT : 2 < T) (qf : Gf) (g : G) : ℂ :=
  sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) (qf * τ g)

private def localResidualFourierMap {T : ℝ} (hT : 2 < T) (qf : Gf) : (G →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (localResidualFourierValues K hζ P hT qf)

private theorem localResidualFourier_ker {T : ℝ} (hT : 2 < T) (qf : Gf) :
    LinearMap.ker gen ≤ LinearMap.ker (localResidualFourierMap K hζ P hT qf) := by
  let w (g : G) : C := r₀ g v₀
  let a := localResidualFourierValues K hζ P hT qf
  have hvalues {I : Type} [Fintype I] (g : I → G) (b : I → ℂ)
      (hsum : (∑ i, b i • w (g i)) = 0) : (∑ i, b i * a (g i)) = 0 := by
    have hproj (g : G) : (C).subtype (w g) = π₀ g (R₀).val := localFourier_translate_val K hζ P hs g
    have hrel : (∑ i : I, b i • π₀ (g i) (R₀).val) = 0 := by
      simpa only [map_sum,map_smul,map_zero,hproj] using congrArg (C).subtype hsum
    exact sourceKPCuspResidualFourierValue_sum_eq_zero_of_local_outgoing_relation K hζ P hs
      g b hrel hT qf
  change LinearMap.ker (Finsupp.linearCombination ℂ w) ≤
    LinearMap.ker (Finsupp.linearCombination ℂ a)
  exact finsupp_kernel_of_relations (A := G) (E := C) w a hvalues

private def localFourierFunctionalWithValues {T : ℝ} (hT : 2 < T) (qf : Gf) :
    {ℓ : C →ₗ[ℂ] ℂ // ∀ g : G, ℓ (r₀ g v₀) = localResidualFourierValues K hζ P hT qf g} := by
  let w (g : G) : C := r₀ g v₀
  let a := localResidualFourierValues K hζ P hT qf
  have hq : Function.Surjective (Finsupp.linearCombination ℂ w) :=
    sourceKPResidualLocalFourierGenerators_surjective K hζ P hs
  have hk : LinearMap.ker (Finsupp.linearCombination ℂ w) ≤
      LinearMap.ker (Finsupp.linearCombination ℂ a) := localResidualFourier_ker K hζ P hs hT qf
  exact generatorLift (A := G) (E := C) w a hq hk

def sourceKPResidualLocalFourierFunctional {T : ℝ} (hT : 2 < T) (qf : Gf) : C →ₗ[ℂ] ℂ :=
  (localFourierFunctionalWithValues K hζ P hs hT qf).val

local notation "ℓ₀" => sourceKPResidualLocalFourierFunctional K hζ P hs

theorem sourceKPResidualLocalFourierFunctional_generator {T : ℝ} (hT : 2 < T) (qf : Gf) (g : G) :
    ℓ₀ hT qf (r₀ g v₀) =
      sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) (qf * τ g) :=
  (localFourierFunctionalWithValues K hζ P hs hT qf).property g

theorem sourceKPResidualLocalFourierFunctional_seed {T : ℝ} (hT : 2 < T) (qf : Gf) :
    ℓ₀ hT qf v₀ = sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) qf := by
  have hv : r₀ (1 : G) v₀ = v₀ := restricted_action_one π₀ C hC v₀
  have hτ : τ (1 : G) = 1 := congrArg Prod.snd (map_one ι₀)
  simpa only [hv,hτ,mul_one] using
    sourceKPResidualLocalFourierFunctional_generator K hζ P hs hT qf (1 : G)

end
end ArtinMatthews
