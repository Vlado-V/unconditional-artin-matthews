module

public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPResidualTranslateInjective
public import ArtinMatthews.SourceKPTraceJacquetFiniteFiber
public import ArtinMatthews.SourceKPCuspResidualFourierRelation
public import ArtinMatthews.SourceKPCuspResidualLocalUpper
public import ArtinMatthews.SourceKPTameCyclicWhittakerUniqueness
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

/-! The compact Fourier test descends through the actual common-level
translate relations to the negative spherical cyclic representation. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic AllowedGenerators QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "G" => SourceFiniteKP2Projective K hζ P.val
local notation "L" => P.val.adicCompletion K
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ
local notation "C" => sourceKPTameSphericalCyclicSpace K hζ S₀ P
local notation "r" => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
local notation "v" => sourceKPTameCyclicSphericalVector K hζ S₀ P
local notation "τ" => fun g : G => Prod.snd (sourceKPAdelicLocalProjective K hζ P.val g)
local notation "N" => fun x : L => sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Upper x)
local notation "ψ" => localFiniteCharacter K P.val

def SourceKPTameResidualTranslateKernel {T : ℝ} (hT : 2 < T) : Prop :=
  ∀ (F : Finset Gf) (ι : Type) [Fintype ι] (g : ι → G)
    (ht : ∀ i, J F ≤ D (τ (g i))) (a : ι → ℂ),
    (∑ i, a i • r (g i) v) = 0 →
    sourceKPResidualTranslateCombination K hζ F (fun i => τ (g i)) ht a hT = 0

private theorem cyclic_generator_surjective :
    Function.Surjective (Finsupp.linearCombination ℂ (fun g : G => r g v)) := by
  intro x
  have hx : x.val ∈ Submodule.span ℂ (Set.range fun g : G =>
      sourceKPTameExteriorInducedRepresentation K hζ S₀ P g
        (sourceKPTameExteriorSphericalSection K hζ S₀ P)) := x.prop
  obtain ⟨l,hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨l, Subtype.ext ?_⟩
  change (C).subtype (Finsupp.linearCombination ℂ (fun g : G => r g v) l) = x.val
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  exact hl

private def cyclic_fourier_values {T : ℝ} (hT : 1 ≤ T) (qf : Gf) (g : G) : ℂ :=
  sourceKPCuspResidualFourierValue K hζ 1 hT (qf * τ g)

private theorem cyclic_fourier_ker {T : ℝ} (hT : 2 < T)
    (hker : SourceKPTameResidualTranslateKernel K hζ S₀ P hT) (qf : Gf) :
    LinearMap.ker (Finsupp.linearCombination ℂ (fun g : G => r g v)) ≤
      LinearMap.ker (Finsupp.linearCombination ℂ
        (cyclic_fourier_values K hζ S₀ P (show 1 ≤ T by linarith) qf)) := by
  classical
  intro l hl
  let F : Finset Gf := l.support.image τ
  have ht (i : l.support) : J F ≤ D (τ i.val) :=
    sourceKPFiniteTranslateLevel_le_conjugate K hζ F
      (Finset.mem_image.mpr ⟨i.val,i.prop,rfl⟩)
  have hz : (∑ i : l.support, l i.val • r i.val v) = 0 := by
    rw [← Finset.sum_subtype l.support (fun _ => Iff.rfl) (fun g => l g • r g v)]
    exact hl
  have hzero := hker F l.support (fun i => i.val) ht (fun i => l i.val) hz
  have hcoeff := sourceKPCuspResidualFourierValue_sum_eq_zero_of_translateCombination
    K hζ F (fun i : l.support => τ i.val) ht (fun i => l i.val) hT hzero 1 qf
  let a := cyclic_fourier_values K hζ S₀ P (show 1 ≤ T by linarith) qf
  change (∑ g ∈ l.support, l g * a g) = 0
  rw [Finset.sum_subtype l.support (fun _ => Iff.rfl) (fun g => l g * a g)]
  exact hcoeff

private theorem cyclic_upper_of_generators (ℓ : C →ₗ[ℂ] ℂ) (x : L)
    (hgen : ∀ g : G, ℓ (r (N x*g) v) = ψ x * ℓ (r g v)) (f : C) :
    ℓ (r (N x) f) = ψ x * ℓ f := by
  let L₀ := Finsupp.linearCombination ℂ (fun g : G => r g v)
  obtain ⟨l,hl⟩ := cyclic_generator_surjective K hζ S₀ P f
  have hEq : (ℓ.comp (r (N x))).comp L₀ = (ψ x • ℓ).comp L₀ := by
    apply Finsupp.lhom_ext
    intro g b
    simp only [LinearMap.comp_apply, L₀, Finsupp.linearCombination_single]
    change ℓ (r (N x) (b • r g v)) = ψ x • ℓ (b • r g v)
    have hng : r (N x) (r g v) = r (N x*g) v :=
      (congrArg (fun A : Module.End ℂ C => A v) (map_mul r (N x) g)).symm
    simp only [map_smul, hng, hgen]
    change b * (ψ x * ℓ (r g v)) = ψ x * (b * ℓ (r g v))
    ring
  change L₀ l = f at hl
  rw [← hl]
  exact congrArg (fun A : (G →₀ ℂ) →ₗ[ℂ] ℂ => A l) hEq

private theorem exists_linear_on_generators {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    (w : ι → E) (a : ι → ℂ)
    (hs : Function.Surjective (Finsupp.linearCombination ℂ w))
    (hk : LinearMap.ker (Finsupp.linearCombination ℂ w) ≤
      LinearMap.ker (Finsupp.linearCombination ℂ a)) :
    ∃ ℓ : E →ₗ[ℂ] ℂ, ∀ i, ℓ (w i) = a i := by
  let ℓ := ((Finsupp.linearCombination ℂ w).liftOfSurjective hs)
    ⟨Finsupp.linearCombination ℂ a,hk⟩
  refine ⟨ℓ,fun i => ?_⟩
  have h := LinearMap.equivOfSurjective_apply hs hk (m := Finsupp.single i 1)
  simpa only [Finsupp.linearCombination_single, one_smul] using h

private theorem cyclic_fourier_values_upper {T : ℝ} (hT : 1 ≤ T) (qf : Gf)
    (hqf : sourceKPAdelicLocalBase K hζ P.val (1,qf) = 1) (x : L) (g : G) :
    cyclic_fourier_values K hζ S₀ P hT qf (N x*g) =
      ψ x * cyclic_fourier_values K hζ S₀ P hT qf g := by
  simpa only [cyclic_fourier_values, sourceKPTraceJacquetFrequencyAt, map_one,
    Units.val_one, one_mul] using
      sourceKPCuspResidualFourierValue_local_upper K hζ P.val 1 hT qf hqf g x

private theorem exists_cyclic_fourier_linear {T : ℝ} (hT : 2 < T)
    (hker : SourceKPTameResidualTranslateKernel K hζ S₀ P hT) (qf : Gf) :
    ∃ ℓ : C →ₗ[ℂ] ℂ, ∀ g : G,
      ℓ (r g v) = cyclic_fourier_values K hζ S₀ P (show 1 ≤ T by linarith) qf g := by
  let w : G → C := fun g => r g v
  let a : G → ℂ := cyclic_fourier_values K hζ S₀ P (show 1 ≤ T by linarith) qf
  have hs : Function.Surjective (Finsupp.linearCombination ℂ w) :=
    cyclic_generator_surjective K hζ S₀ P
  have hk : LinearMap.ker (Finsupp.linearCombination ℂ w) ≤
      LinearMap.ker (Finsupp.linearCombination ℂ a) :=
    cyclic_fourier_ker K hζ S₀ P hT hker qf
  exact exists_linear_on_generators w a hs hk

private theorem cyclic_fourier_linear_upper {T : ℝ} (hT : 1 ≤ T) (qf : Gf)
    (hqf : sourceKPAdelicLocalBase K hζ P.val (1,qf) = 1) (ℓ : C →ₗ[ℂ] ℂ)
    (hw : ∀ g : G, ℓ (r g v) = cyclic_fourier_values K hζ S₀ P hT qf g)
    (x : L) (f : C) :
    ℓ (r (N x) f) = ψ x * ℓ f := by
  apply cyclic_upper_of_generators K hζ S₀ P ℓ x _ f
  intro g
  calc
    ℓ (r (N x*g) v) = cyclic_fourier_values K hζ S₀ P hT qf (N x*g) := hw (N x*g)
    _ = ψ x * cyclic_fourier_values K hζ S₀ P hT qf g :=
      cyclic_fourier_values_upper K hζ S₀ P hT qf hqf x g
    _ = _ := congrArg (ψ x * ·) (hw g).symm

theorem sourceKPTameResidualFourierFunctional_exists_of_translateKernel
    {T : ℝ} (hT : 2 < T) (hker : SourceKPTameResidualTranslateKernel K hζ S₀ P hT)
    (qf : Gf) (hqf : sourceKPAdelicLocalBase K hζ P.val (1,qf) = 1) :
    ∃ ℓ : C →ₗ[ℂ] ℂ,
      (∀ g : G, ℓ (r g v) =
        sourceKPCuspResidualFourierValue K hζ 1 (show 1 ≤ T by linarith) (qf * τ g)) ∧
      ∀ (x : L) (f : C), ℓ (r (N x) f) = ψ x * ℓ f := by
  have hT' : 1 ≤ T := by linarith
  obtain ⟨ℓ,hw⟩ := exists_cyclic_fourier_linear K hζ S₀ P hT hker qf
  have hupper : ∀ (x : L) (f : C), ℓ (r (N x) f) = ψ x * ℓ f :=
    cyclic_fourier_linear_upper K hζ S₀ P hT' qf hqf ℓ hw
  exact ⟨ℓ,hw,hupper⟩

theorem sourceKPTameResidualFourierValue_factor_of_translateKernel
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    {T : ℝ} (hT : 2 < T) (hker : SourceKPTameResidualTranslateKernel K hζ S₀ P hT)
    (qf : Gf) (hqf : sourceKPAdelicLocalBase K hζ P.val (1,qf) = 1) (g : G) :
    sourceKPCuspResidualFourierValue K hζ 1 (show 1 ≤ T by linarith) (qf * τ g) =
      sourceKPCuspResidualFourierValue K hζ 1 (show 1 ≤ T by linarith) qf *
        sourceKPTameCyclicWhittakerValue K hζ S₀ P hS g := by
  obtain ⟨ℓ,hw,hupper⟩ :=
    sourceKPTameResidualFourierFunctional_exists_of_translateKernel K hζ S₀ P hT hker qf hqf
  have h := sourceKPTameCyclicWhittakerFunctional_eq_smul K hζ S₀ P hS ℓ hupper
  have hτ : τ (1 : G) = 1 :=
    congrArg Prod.snd (map_one (sourceKPAdelicLocalProjective K hζ P.val))
  have hr : r (1 : G) v = v := by rw [map_one]; rfl
  have hv : ℓ v = sourceKPCuspResidualFourierValue K hζ 1 (show 1 ≤ T by linarith) qf := by
    simpa only [hr, hτ, mul_one] using hw 1
  have hg := congrArg (fun A : C →ₗ[ℂ] ℂ => A (r g v)) h
  rw [hw g, hv] at hg
  exact hg

end
end ArtinMatthews
