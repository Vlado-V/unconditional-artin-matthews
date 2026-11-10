module

public import ArtinMatthews.SourceKPTranslateCompactTrace
public import ArtinMatthews.SourceKPCompactC2Core
public import ArtinMatthews.SourceKPAutomorphicCompactTopology
public import ArtinMatthews.SourceKPCompactRationalTransport
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Literal finite Hecke traces preserve the actual compact scalar core. -/
namespace ArtinMatthews
open NumberField Matrix Topology SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing ContDiff BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "U" => SourceKPArchUpperHalfSpace K
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "C2" => sourceKPCompactC2Core K hζ
local notation "q" => sourceKPTranslateUpperMk K hζ T

local notation "φ[" t ", " ht "]" => sourceKPFiniteRightTranslateMap K hζ T t ht
local notation "π[" t ", " ht "]" => sourceKPTranslateAutomorphicCompactMap K hζ T t ht
local notation "L[" t ", " ht ", " b "]" => {c : FJ // φ[t, ht] c = b}

theorem sourceKPTranslateAutomorphicCompactMap_preimage_isCompact (t : Gf) (ht : J ≤ D t)
    (S : Set Y) (hS : IsCompact S) : IsCompact (π[t, ht] ⁻¹' S) := by
  obtain ⟨I,hI⟩ := sourceKPCompact_finite_chart_cover K hζ S hS
  let C (i : F × U) : Set YJ :=
    ⋃ c : L[t, ht, i.1], (fun p : U => q (p,c.val)) ''
      closure ((sourceKPUpperFiniteChart K hζ i.1 i.2).domain : Set U)
  have hC (i : F × U) : IsCompact (C i) := by
    apply isCompact_iUnion
    intro c
    exact (sourceKPUpperFiniteChart K hζ i.1 i.2).isCompact_closure.image
      ((sourceKPTranslateUpperMk_isOpenQuotientMap K hζ T).continuous.comp
        (continuous_id.prodMk continuous_const))
  have hbig : IsCompact (⋃ i ∈ I, C i) := I.finite_toSet.isCompact_biUnion fun i _ => hC i
  apply hbig.of_isClosed_subset
    (hS.isClosed.preimage (sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t ht))
  intro y hy
  induction y using Quotient.inductionOn with
  | _ x =>
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI hy)
    obtain ⟨hmem,p,hp⟩ := Set.mem_iUnion.mp hi
    have he : sourceKPUpperToCompact K hζ i.1 p.val =
        sourceKPUpperToCompact K hζ (φ[t, ht] x.2) x.1 := hp
    obtain ⟨γ,hfin,harch⟩ :=
      (sourceKPUpperToCompact_eq_iff_rational K hζ i.1 (φ[t, ht] x.2) p.val x.1).mp he
    let c : FJ := sourceKPRationalFiniteMap K hζ γ • x.2
    have hc : φ[t, ht] c = i.1 := by
      unfold c
      rw [sourceKPFiniteRightTranslateMap_smul]
      exact hfin
    have hq : q (p.val,c) = q x := by
      apply Quotient.sound
      exact MulAction.mem_orbit_iff.mpr ⟨γ,Prod.ext harch rfl⟩
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hmem,
      Set.mem_iUnion.mpr ⟨⟨c,hc⟩,p.val,subset_closure p.prop,hq⟩⟩⟩

theorem sourceKPTranslateAutomorphicCompactMap_compactSupport (t : Gf) (ht : J ≤ D t)
    (f : Y → ℂ) (hf : HasCompactSupport f) : HasCompactSupport (f ∘ π[t, ht]) := by
  apply IsCompact.of_isClosed_subset
    (sourceKPTranslateAutomorphicCompactMap_preimage_isCompact K hζ T t ht _ hf) isClosed_closure
  apply closure_minimal
  · exact fun _ hx => subset_closure hx
  · exact isClosed_closure.preimage
      (sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t ht)

theorem sourceKPTranslateCompactTrace_compactSupport (t : Gf) (ht : J ≤ D t)
    (v : YJ → ℂ) (hv : HasCompactSupport v) :
    HasCompactSupport (sourceKPTranslateCompactTrace K hζ T t ht v) := by
  have hK : IsCompact (π[t, ht] '' tsupport v) :=
    hv.image (sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t ht)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro y hy
  by_contra h
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  apply hy
  rw [sourceKPTranslateCompactTrace_upper]
  apply Finset.sum_eq_zero
  intro c _
  by_contra hc
  have hq : π[t, ht] (q (p,c.val)) = sourceKPUpperToCompact K hζ b p := by
    rw [sourceKPTranslateAutomorphicCompactMap_upperMk]
    exact congrArg (fun d => sourceKPUpperToCompact K hζ d p) c.prop
  exact h ⟨q (p,c.val),subset_closure hc,hq⟩

private def gramFun (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f : Y → ℂ) : Y → ℂ :=
  sourceKPTranslateCompactTrace K hζ T t ht (f ∘ π[u, hu])

private theorem gramFun_upper (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f : Y → ℂ) (b : F) (p : U) :
    gramFun K hζ T t ht u hu f (sourceKPUpperToCompact K hζ b p) =
      ∑ c : L[t, ht, b], f (sourceKPUpperToCompact K hζ (φ[u, hu] c.val) p) := by
  rw [gramFun, sourceKPTranslateCompactTrace_upper]
  simp only [Function.comp_apply, sourceKPTranslateAutomorphicCompactMap_upperMk]

private theorem gramFun_chart (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f : Y → ℂ) (b : F) :
    sourceKPCompactChartPullback K hζ (gramFun K hζ T t ht u hu f) b =
      fun x => ∑ c : L[t, ht, b], sourceKPCompactChartPullback K hζ f (φ[u, hu] c.val) x := by
  funext x
  by_cases hx : x ∈ productUpper (InfinitePlace K)
  · simp only [sourceKPCompactChartPullback,hx,ite_true,gramFun_upper]
  · simp only [sourceKPCompactChartPullback,hx,ite_false,Finset.sum_const_zero]

def sourceKPTranslateCoreGram (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u) : C2 →ₗ[ℂ] C2 where
  toFun f := ⟨gramFun K hζ T t ht u hu f.val,
    sourceKPTranslateCompactTrace_continuous K hζ T t ht _
      (f.prop.1.comp (sourceKPTranslateAutomorphicCompactMap_continuous K hζ T u hu)),
    sourceKPTranslateCompactTrace_compactSupport K hζ T t ht _
      (sourceKPTranslateAutomorphicCompactMap_compactSupport K hζ T u hu f.val f.prop.2.1),
    fun b => by
      rw [gramFun_chart]
      exact ContDiffOn.sum (fun c _ => f.prop.2.2 (φ[u, hu] c.val))⟩
  map_add' f g := by
    apply Subtype.ext
    funext y
    obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
    change gramFun K hζ T t ht u hu (f.val + g.val) (sourceKPUpperToCompact K hζ b p) =
      gramFun K hζ T t ht u hu f.val (sourceKPUpperToCompact K hζ b p) +
        gramFun K hζ T t ht u hu g.val (sourceKPUpperToCompact K hζ b p)
    simp only [gramFun_upper,Pi.add_apply,Finset.sum_add_distrib]
  map_smul' a f := by
    apply Subtype.ext
    funext y
    obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
    change gramFun K hζ T t ht u hu (a • f.val) (sourceKPUpperToCompact K hζ b p) =
      a • gramFun K hζ T t ht u hu f.val (sourceKPUpperToCompact K hζ b p)
    simp only [gramFun_upper,Pi.smul_apply,Finset.smul_sum]

theorem sourceKPTranslateCoreGram_val (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f : C2) :
    (sourceKPTranslateCoreGram K hζ T t ht u hu f).val =
      sourceKPTranslateCompactTrace K hζ T t ht (f.val ∘ π[u, hu]) := rfl

theorem sourceKPTranslateCoreGram_upper (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f : C2) (b : F) (p : U) :
    (sourceKPTranslateCoreGram K hζ T t ht u hu f).val (sourceKPUpperToCompact K hζ b p) =
      ∑ c : L[t, ht, b], f.val (sourceKPUpperToCompact K hζ (φ[u, hu] c.val) p) :=
  gramFun_upper K hζ T t ht u hu f.val b p

theorem sourceKPTranslateCoreGram_chart (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f : C2) (b : F) :
    sourceKPCompactChartPullback K hζ (sourceKPTranslateCoreGram K hζ T t ht u hu f).val b =
      fun x => ∑ c : L[t, ht, b], sourceKPCompactChartPullback K hζ f.val (φ[u, hu] c.val) x :=
  gramFun_chart K hζ T t ht u hu f.val b

theorem sourceKPTranslateCoreGram_character (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f : C2)
    (hf : ∀ (z : rootsOfUnity 3 K) (y : Y),
      f.val (z • y) = (sourceKPAdelicCentralComplex K hζ z : ℂ) * f.val y)
    (z : rootsOfUnity 3 K) (y : Y) :
    (sourceKPTranslateCoreGram K hζ T t ht u hu f).val (z • y) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        (sourceKPTranslateCoreGram K hζ T t ht u hu f).val y := by
  rw [sourceKPTranslateCoreGram_val, sourceKPTranslateCompactTrace_center]
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  simp only [sourceKPTranslateCompactTrace_upper, Function.comp_apply,
    sourceKPTranslateAutomorphicCompactMap_center, hf, Finset.mul_sum]

end
end ArtinMatthews
