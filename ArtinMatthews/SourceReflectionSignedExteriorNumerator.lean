module

public import ArtinMatthews.SourceReflectionSignedExteriorSupport
public import ArtinMatthews.SourceReflectionNumeratorReindex
public import ArtinMatthews.SourceReflectionFieldFrequency
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

/-! A surviving signed frequency gives the actual supported numerator
index. The inactive primes retain both their quotient and remainder. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "a" => sourcePrimeExponentUnit K hζ S₀
local notation "b" => fun f d => a (sourceReflectionActiveExponents K S₀ f + d)
local notation "N" => sourceReflectionIntegralNumerator K S₀
local notation "Πext" => sourceReflectionSignedExteriorProduct K S₀ hζ hS
local notation "Supported" => SourceReflectionSignedExteriorFrequencySupport K S₀ hζ

include hζ in
theorem sourceReflectionIntegralNumerator_exponents_eq_order (B : Kˣ)
    (u : SourceReflectionFieldFrequency K S₀ B) (P : Pr) :
    (sourceElementExponents K S₀ (N B u).val (N B u).property P : ℤ) =
      exteriorPrincipalValuation P.val (u.val * B ^ 2) := by
  have h := sourceElementExponents_valuation K S₀ hζ (N B u).val (N B u).property P
  rw [← sourceReflectionIntegralNumerator_fieldUnit K S₀ B u,
    sourceExteriorPrincipalValuation_eq_neg_log, sourceNonzeroFrequencyFieldUnit_val,
    h, WithZero.log_exp, neg_neg]

theorem sourceReflectionSplitNumerator_inactive_coordinates (f : Finset Pr) (d : E)
    (e : SourceReflectionNumerator K S₀ d) (P : Pr) (hP : P ∉ f) :
    let i := sourceReflectionSplitNumerator K S₀ f d e
    i.val.1.val P = 0 ∧ i.val.2.1 P = e.val P / 3 ∧ i.val.2.2.val P = e.val P % 3 := by
  simp [sourceReflectionSplitNumerator, Finsupp.mapRange_apply, hP]

theorem sourceReflectionSignedExteriorFrequencySupport_exists_supportedTerm (f : Finset Pr) (d : E)
    (ν : Kˣ) (hν : Supported f d ν) :
    ∃ u : SourceReflectionFieldFrequency K S₀ (b f d), u.val = ν ∧
      ∃ i : SourceReflectionSupportedTermIndex K S₀ f d,
        (sourceReflectionCombineNumerator K S₀ f d i).val =
          sourceElementExponents K S₀ (N (b f d) u).val (N (b f d) u).property := by
  let u : SourceReflectionFieldFrequency K S₀ (b f d) :=
    ⟨ν, (sourceReflectionFieldUnit_mem_integer_iff K S₀ _).mpr hν.1⟩
  let e : E := sourceElementExponents K S₀ (N (b f d) u).val (N (b f d) u).property
  have he (P : Pr) : (e P : ℤ) = exteriorPrincipalValuation P.val (ν * (b f d) ^ 2) :=
    sourceReflectionIntegralNumerator_exponents_eq_order K S₀ hζ (b f d) u P
  have hm (P : Pr) : e P % 3 ≤ 1 := by
    have hP := hν.2.1 P
    rw [← he] at hP
    exact_mod_cast hP
  have hz (P : Pr) (hP : P ∈ d.support) : e P = 0 := by
    have h := (he P).trans (hν.2.2 P hP)
    exact_mod_cast h
  let e₀ : SourceReflectionNumerator K S₀ d := ⟨e, hm, hz⟩
  refine ⟨u, rfl, sourceReflectionSplitNumerator K S₀ f d e₀, ?_⟩
  exact congrArg Subtype.val (sourceReflectionCombineNumerator_split K S₀ f d e₀)

theorem sourceReflectionSignedExteriorProduct_nonzero_supportedTerm (h d : E) (f : Finset Pr)
    (hd : sourceReflectionIsSquarefree d) (hhd : Disjoint h.support d.support) (hfd : Disjoint f d.support)
    (ν : Kˣ) (hν : Πext (h + d) (f ∪ d.support) ν ≠ 0) :
    ∃ u : SourceReflectionFieldFrequency K S₀ (b f d), u.val = ν ∧
      ∃ i : SourceReflectionSupportedTermIndex K S₀ f d,
        (sourceReflectionCombineNumerator K S₀ f d i).val =
          sourceElementExponents K S₀ (N (b f d) u).val (N (b f d) u).property :=
  sourceReflectionSignedExteriorFrequencySupport_exists_supportedTerm K S₀ hζ f d ν
    (sourceReflectionSignedExteriorProduct_nonzero_support K S₀ hζ hS h d f hd hhd hfd ν hν)

end
end ArtinMatthews.SourceEulerAssembly
