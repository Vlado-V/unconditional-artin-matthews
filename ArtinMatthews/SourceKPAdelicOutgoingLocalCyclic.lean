module

public import ArtinMatthews.SourceKPAdelicOutgoingLocalRelation
public import ArtinMatthews.SourceKPJacquetSmoothAverage
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

/-! The cyclic span of the actual local section maps linearly and
faithfully to the adelic principal series by all-remainder evaluation.
The map intertwines the actual local right translations. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

private theorem sourceKPOutgoingOrbit_seed_mem {G U : Type*} [Group G] [AddCommMonoid U]
    [Module ℂ U] (π : Representation ℂ G U) (v : U) :
    v ∈ Submodule.span ℂ (Set.range (fun a : G => π a v)) := by
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  change π 1 v = v
  rw [map_one, Module.End.one_apply]

private theorem sourceKPOutgoingOrbit_invariant {G U : Type*} [Group G] [AddCommMonoid U]
    [Module ℂ U] (π : Representation ℂ G U) (v : U) (a : G) (f : U)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun b : G => π b v))) :
    π a f ∈ Submodule.span ℂ (Set.range (fun b : G => π b v)) := by
  let C := Submodule.span ℂ (Set.range (fun b : G => π b v))
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b,rfl⟩ := hf
    apply Submodule.subset_span
    refine ⟨a*b, ?_⟩
    change π (a*b) v = π a (π b v)
    rw [map_mul, Module.End.mul_apply]
  | zero => simpa only [map_zero] using C.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using C.add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using C.smul_mem a hx

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "S" => (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K)))
local notation "G₀" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "G" => SourceKPAdelicProjective K hζ
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "p₀" => sourceKPAdelicOutgoingSingletonPlace K P
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "Vₚ" => SourceKPAdelicPrincipalSeries K hζ
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ S
local notation "R" => sourceKPAdelicOutgoingRegularizedSection K hζ
local notation "R₀" => sourceKPAdelicOutgoingRegularizedLocalSection K hζ P
local notation "ρ" => sourceKPAdelicPrincipalSeriesRepresentation K hζ
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P
local notation "A" => sourceKPAdelicOutgoingLocalEvaluation K hζ P
local notation "B" => sourceKPAdelicOutgoingLocalInducedEvaluation K hζ P
local notation "I₀" =>
  (fun (s : ℂ) (hs : 0 < Complex.re s) => sourceAlgebraicInducedSpace B₀ (ρ₀ s hs))
local notation "π₀" =>
  (fun (s : ℂ) (hs : 0 < Complex.re s) => sourceAlgebraicInducedRepresentation B₀ (ρ₀ s hs))

local instance sourceKPAdelicOutgoingLocalCyclicTorusAddCommGroup (s : ℂ) :
    AddCommGroup (V s) := Submodule.addCommGroup _

local instance sourceKPAdelicOutgoingLocalCyclicPrincipalAddCommGroup (s : ℂ) :
    AddCommGroup (Vₚ s) := Submodule.addCommGroup _

local instance sourceKPAdelicOutgoingLocalCyclicBorelAddCommGroup (s : ℂ) (hs : 0 < s.re) :
    AddCommGroup (W s hs) := Submodule.addCommGroup _

def sourceKPAdelicOutgoingRegularizedLocalCyclic (s : ℂ) (hs : 0 < s.re) :
    Submodule ℂ (I₀ s hs) :=
  Submodule.span ℂ (Set.range (fun a : G₀ => π₀ s hs a (R₀ s hs).val))

local notation "C" => sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P

def sourceKPAdelicOutgoingRegularizedLocalCyclicVector (s : ℂ) (hs : 0 < s.re) : C s hs :=
  ⟨(R₀ s hs).val, sourceKPOutgoingOrbit_seed_mem (π₀ s hs) (R₀ s hs).val⟩

theorem sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant (s : ℂ) (hs : 0 < s.re)
    (a : G₀) (f : I₀ s hs) (hf : f ∈ C s hs) : π₀ s hs a f ∈ C s hs :=
  sourceKPOutgoingOrbit_invariant (π₀ s hs) (R₀ s hs).val a f hf

local notation "π" =>
  (fun (s : ℂ) (hs : 0 < Complex.re s) => sourceKPJacquetRight K hζ P (ρ₀ s hs) (C s hs)
    (sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P s hs))

theorem sourceKPAdelicOutgoingLocalCyclicEvaluation_mem_range (s : ℂ) (hs : 0 < s.re)
    (f : I₀ s hs) (hf : f ∈ C s hs) : B s hs f ∈ LinearMap.range (A s) := by
  change f ∈ Submodule.span ℂ (Set.range (fun a : G₀ => π₀ s hs a (R₀ s hs).val)) at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a,rfl⟩ := hf
    rw [sourceKPAdelicOutgoingLocalEvaluation_translate K hζ P s hs]
    exact LinearMap.mem_range_self _ _
  | zero => simpa only [map_zero] using (LinearMap.range (A s)).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (LinearMap.range (A s)).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (LinearMap.range (A s)).smul_mem a hx

def sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal (s : ℂ) (hs : 0 < s.re) :
    C s hs →ₗ[ℂ] Vₚ (-s) :=
  LinearMap.codRestrictOfInjective ((B s hs).comp (C s hs).subtype) (A s)
    (sourceKPAdelicOutgoingLocalEvaluation_injective K hζ P s)
    (fun f => sourceKPAdelicOutgoingLocalCyclicEvaluation_mem_range K hζ P s hs f.val f.property)

local notation "H" => sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal K hζ P

theorem sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal_evaluation (s : ℂ) (hs : 0 < s.re)
    (f : C s hs) : A s (H s hs f) = B s hs f.val :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ f

theorem sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal_injective (s : ℂ) (hs : 0 < s.re) :
    Function.Injective (H s hs) := by
  intro f g h
  apply Subtype.ext
  apply sourceKPAdelicOutgoingLocalInducedEvaluation_injective K hζ P s hs
  exact (sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal_evaluation K hζ P s hs f).symm.trans
    ((congrArg (⇑(A s)) h).trans
      (sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal_evaluation K hζ P s hs g))

theorem sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal_seed (s : ℂ) (hs : 0 < s.re) :
    H s hs (sourceKPAdelicOutgoingRegularizedLocalCyclicVector K hζ P s hs) = R s hs := by
  apply sourceKPAdelicOutgoingLocalEvaluation_injective K hζ P s
  refine (sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal_evaluation K hζ P s hs _).trans ?_
  funext q r
  exact sourceKPAdelicOutgoingRegularizedLocalSection_apply K hζ P s hs q r

theorem sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal_right (s : ℂ) (hs : 0 < s.re)
    (a : G₀) (f : C s hs) :
    H s hs (π s hs a f) = ρ (-s) (ι₀ a) (H s hs f) := by
  let f' : C s hs := π s hs a f
  change H s hs f' = _
  apply sourceKPAdelicOutgoingLocalEvaluation_injective K hζ P s
  funext q r
  have h := congrFun (congrFun
    (sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal_evaluation K hζ P s hs f) (q*a)) r
  have h' := congrFun (congrFun
    (sourceKPAdelicOutgoingRegularizedLocalCyclicToGlobal_evaluation K hζ P s hs f') q) r
  change (H s hs f).val (ι₀ (q*a)*r.val) = (f.val.val (q*a)).val r at h
  change (H s hs f').val (ι₀ q*r.val) = (f.val.val (q*a)).val r at h'
  change (H s hs f').val (ι₀ q*r.val) = (H s hs f).val ((ι₀ q*r.val)*ι₀ a)
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P a r.val (r.property p₀)
  have he : ι₀ (q*a)*r.val = (ι₀ q*r.val)*ι₀ a := by
    rw [map_mul ι₀,mul_assoc,hc.eq,← mul_assoc]
  exact h'.trans (h.symm.trans (congrArg (fun g : G => (H s hs f).val g) he))

end
end ArtinMatthews
