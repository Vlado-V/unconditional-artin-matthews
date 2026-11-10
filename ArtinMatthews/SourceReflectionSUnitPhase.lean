module

public import ArtinMatthews.SourceReflectionSUnitHilbert
public import ArtinMatthews.SourceReflectionRowClass
public import ArtinMatthews.SLocalPaperHilbertNormalization
public import ArtinMatthews.SourcePrimeExponentValuation
public import ArtinMatthews.SourceQuadraticHeckeSymbols
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertProductFormula
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.PNatToNat
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The row S-unit correction is a unitary character on the original
finite S-local sixth-power classes. This leaves the exterior character
as the exact zero-extended product at the row primes. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity GlobalClassFieldTheory.GlobalClassFields
open AllowedGenerators SIntegerPrincipalization SIntegerAllowedReciprocity VaryingKummerAnalytic AngularLambda
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "D" => SourcePrimeExponents K S₀
local notation "X" => exteriorUnitSubgroup S
local notation "H" => sourceReflectionSexticHilbert K hζ
local notation "E" => sourceReflectionSixthRootValue K hζ
local notation "Q" => SLocalRingPowerClasses K 6 S
local notation "classOf" => sLocalRingGlobalClassMap K 6 S
local notation "rootsEquiv" => nthRootsSubgroupEquivRootsOfUnity K 6

def sourceReflectionSUnitClassPhase (u : X) (a : Q) : ℂ :=
  E ((rootsEquiv).symm (paperSourceHilbertForm K hζ S a (classOf u.val)))⁻¹

theorem sourceReflectionSUnitClassPhase_norm (u : X) (a : Q) :
    ‖sourceReflectionSUnitClassPhase K hζ S₀ u a‖ = 1 := by
  let z := ((rootsEquiv).symm (paperSourceHilbertForm K hζ S a (classOf u.val)))⁻¹
  let v : ℂˣ := Units.map (sourceComplexEmbedding hζ).toMonoidHom z.val
  have hv : v ∈ rootsOfUnity 6 ℂ := by
    change v ^ 6 = 1
    rw [← map_pow, z.property,map_one]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity hv

private theorem exteriorHilbert_mulSupport (u : X) (e : D) :
    Function.mulSupport (fun P => H P u.val (sourcePrimeExponentUnit K hζ S₀ e)) ⊆
      (↑(S ∪ e.support.image Subtype.val) : Set (HeightOneSpectrum (𝓞 K))) := by
  intro P hP
  by_contra hn
  have hPS : P ∉ S := fun h => hn (Finset.mem_union_left _ h)
  have he : e ⟨P,hPS⟩ = 0 :=
    Finsupp.notMem_support_iff.mp fun h => hn (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨⟨P,hPS⟩,h,rfl⟩))
  have hu := (sourceExteriorPrincipalValuation_eq_zero_iff K P u.val).mp (u.property P hPS)
  have ha : P.valuation K (sourcePrimeExponentUnit K hζ S₀ e : K) = 1 := by
    rw [sourcePrimeExponentUnit_val,
      sourcePrimeExponentGenerator_valuation K hζ S₀ e ⟨P,hPS⟩,he,Int.natCast_zero,neg_zero,
      WithZero.exp_zero]
  exact hP (finitePlaceHilbertSymbol_eq_one_of_valuation_eq_one K 6 (by norm_num)
    (sourceSixRoots K hζ) u.val (sourcePrimeExponentUnit K hζ S₀ e) P hu ha
    (sourceSix_unit_valuation K S₀ P hPS))

theorem sourceReflectionExponentResidueValue_sUnit_eq_classPhase (u : X) (e : D) :
    reflectionExponentResidueValue K hζ S₀ e (sourceExteriorUnitToSourceRing K S₀ u) =
      sourceReflectionSUnitClassPhase K hζ S₀ u (classOf (sourcePrimeExponentUnit K hζ S₀ e)) := by
  let b := sourcePrimeExponentUnit K hζ S₀ e
  let V := e.support.image (fun P : SourceExteriorPrime K S₀ => P.val)
  let F : HeightOneSpectrum (𝓞 K) → nthRootsSubgroup K (probeSix : ℕ) :=
    fun P => H P u.val b
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  have hDis : Disjoint S V := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    obtain ⟨Pext,_,rfl⟩ := Finset.mem_image.mp hV
    exact Pext.property hP
  have hI (v : InfinitePlace K) : infinitePlaceHilbertSymbol K probeSix v u.val b = 1 :=
    infinitePlaceHilbertSymbol_eq_one_of_isComplex K probeSix v u.val b (IsTotallyComplex.isComplex v)
  have hall := hilbertSymbol_allPlaces_product_eq_one K probeSix (by norm_num)
    (sourceSixRoots K hζ) u.val b
  change (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K probeSix v u.val b) *
    (∏ᶠ P, F P) = 1 at hall
  rw [finprod_eq_prod_of_mulSupport_subset F (exteriorHilbert_mulSupport K hζ S₀ u e),
    Finset.prod_union hDis] at hall
  simp only [hI,Finset.prod_const_one,one_mul] at hall
  have hext : (∏ P ∈ V, F P) = (∏ P ∈ S, F P)⁻¹ := by
    calc
      _ = (∏ P ∈ S, F P)⁻¹ * ((∏ P ∈ S, F P) * (∏ P ∈ V, F P)) :=
        (inv_mul_cancel_left _ _).symm
      _ = _ := by rw [hall,mul_one]
  have hphase : (rootsEquiv).symm (paperSourceHilbertForm K hζ S (classOf b) (classOf u.val)) =
      ∏ P ∈ S, F P := by
    let z : nthRootsSubgroup K 6 := probeHilbertSProduct K 6 (by norm_num)
      (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) S u.val b
    have hz : paperSourceHilbertForm K hζ S (classOf b) (classOf u.val) = (rootsEquiv) z :=
      paperSourceHilbertForm_global_eq_SProduct K hζ S b u.val
    calc
      _ = (rootsEquiv).symm ((rootsEquiv) z) := congrArg (rootsEquiv).symm hz
      _ = z := (rootsEquiv).symm_apply_apply z
      _ = _ := by
        change (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K probeSix v u.val b) *
          (∏ P ∈ S, F P) = ∏ P ∈ S, F P
        simp only [hI,Finset.prod_const_one,one_mul]
  change (∏ P ∈ e.support, sourcePrimeExponentLocalWeight K hζ S₀
    (reflectionPrimeCharacters K hζ S₀) P (e P) (sourceExteriorUnitToSourceRing K S₀ u)) = _
  simp_rw [sourceReflectionLocalSUnitWeight_eq_hilbert K hζ S₀ u e]
  rw [← map_prod]
  have hProd : (∏ P ∈ V, F P) = ∏ P ∈ e.support, F P.val :=
    Finset.prod_image (fun P _ P' _ h => Subtype.ext h)
  change E (∏ P ∈ e.support, F P.val) = sourceReflectionSUnitClassPhase K hζ S₀ u (classOf b)
  calc
    _ = E (∏ P ∈ V, F P) := congrArg E hProd.symm
    _ = E ((∏ P ∈ S, F P)⁻¹) := congrArg E hext
    _ = _ := congrArg (fun a : nthRootsSubgroup K (probeSix : ℕ) => E a⁻¹) hphase.symm

theorem sourceReflectionCanonicalRow_residue_twist
    (e f : D) (u : ExteriorUnitSixthClasses S) :
    reflectionExponentResidueValue K hζ S₀ f (sourceReflectionCanonicalRow K S₀ hζ e u) =
      sourceReflectionSUnitClassPhase K hζ S₀ (sourceExteriorUnitSixthRepresentative S u)
        (classOf (sourcePrimeExponentUnit K hζ S₀ f)) *
        reflectionExponentResidueValue K hζ S₀ e (sourcePrimeExponentGenerator K hζ S₀ f) := by
  let u₀ := sourceExteriorUnitSixthRepresentative S u
  let x : PrincipalIntegerRing (sourceHilbertSeed K S₀) := sourceExteriorUnitToSourceRing K S₀ u₀
  let y : PrincipalIntegerRing (sourceHilbertSeed K S₀) := sourcePrimeExponentGenerator K hζ S₀ e
  change reflectionExponentResidueValue K hζ S₀ f (x * y) = _
  exact (sourceReflectionExponentResidueValue_mul K S₀ hζ f x y).trans
    (congrArg₂ (· * ·)
      (sourceReflectionExponentResidueValue_sUnit_eq_classPhase K hζ S₀ u₀ f)
      (sourceReflectionExponentResidueValue_symmetric K S₀ hζ f e))

end
end ArtinMatthews.SourceEulerAssembly
