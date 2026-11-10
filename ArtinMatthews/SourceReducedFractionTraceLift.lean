module

public import ArtinMatthews.SourceReducedFractionLabels
public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencyLabels
public import ArtinMatthews.SourceFractionalIdealDualValuation
public import ArtinMatthews.SourceFrequencyUnitPart
public import ArtinMatthews.SourcePrincipalBallQuotientKernel
public import ArtinMatthews.SourceSLocalExponentPoisson
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Finite-place phase control by actual residue lifts. Adjusting a lift
inside its source quotient lets us use the checked integral-coordinate
sieve even for the original fixed product generators. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain AllowedGenerators FractionalIdeal SIntegerPrincipalization
open StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F}

local notation "S" => sourceHilbertSet F S₀
local notation "T" => sourceHilbertSeed F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "M" => sourcePrimeExponentIdeal F S₀
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

theorem sourceReducedDenominator_valuation (hζ : IsPrimitiveRoot ζ 12)
    (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e})
    (e : E) (P : SourceExteriorPrime F S₀) :
    P.val.valuation F (a e : F) = WithZero.exp (-(e P : ℤ)) := by
  have he : sourceElementExponents F S₀ (a e) (ha e) = e :=
    (sourcePrimeExponentRingIdealEquiv F S₀).injective (Subtype.ext
      ((sourceElementExponents_ideal F S₀ (a e) (ha e)).trans (hgen e).symm))
  rw [sourceElementExponents_valuation F S₀ hζ (a e) (ha e) P, he]

/-- A lift of the actual numerator class can be chosen so that dividing
by the generator and a fixed exterior unit gives an element of the genuine
trace dual. Both nonunit exclusion and the unit-ideal label stay literal. -/
theorem exists_sourceReducedFraction_traceLift (hζ : IsPrimitiveRoot ζ 12)
    (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e})
    (htrace : traceBadPlaces F ⊆ S) (δ : 𝓞 F) (hδ : δ ≠ 0)
    (hδS : ∀ P : HeightOneSpectrum (𝓞 F), P ∉ S → P.valuation F (δ : F) = 1)
    (p : SourceReducedFractionLabel F S₀ a) :
    ∃ x : R, Ideal.Quotient.mk (Ideal.span {a p.1}) x = (p.2 : R ⧸ Ideal.span {a p.1}) ∧
      (x : F) / ((a p.1 : F) * (δ : F)) ∈ FractionalIdeal.dual ℤ ℚ (M p.1 : FI) := by
  let b : F := (a p.1 : F) * (δ : F)
  have hb : b ≠ 0 := mul_ne_zero (Subtype.coe_injective.ne (ha p.1)) (Subtype.coe_injective.ne hδ)
  let e (v : S) : ℤ := -(WithZero.log (v.val.valuation F b)) - (sourceDifferentExponent F v.val : ℤ)
  let J : Ideal R := (M p.1).map (algebraMap (𝓞 F) R)
  have hJ : J = Ideal.span {a p.1} := hgen p.1
  let ev := Ideal.quotEquivOfEq hJ
  have hq := sourcePrincipalBallIdealToQuotient_surjective F T e (M p.1)
    (sourcePrimeExponentIdeal_exterior F S₀ p.1).2
  obtain ⟨x, hx⟩ := hq (ev.symm (p.2 : R ⧸ Ideal.span {a p.1}))
  let y : R := sourcePrincipalBallIdealToInteger F T e x
  have hxy : Ideal.Quotient.mk J y = ev.symm (p.2 : R ⧸ Ideal.span {a p.1}) := hx
  have hy : Ideal.Quotient.mk (Ideal.span {a p.1}) y = (p.2 : R ⧸ Ideal.span {a p.1}) := by
    rw [← Ideal.quotEquivOfEq_mk hJ y, hxy]
    exact ev.apply_symm_apply _
  refine ⟨y, hy, ?_⟩
  rw [sourceFractionalIdeal_dual_mem_iff F _ (FractionalIdeal.coeIdeal_ne_zero.mpr
    (sourcePrimeExponentIdeal_ne_bot F S₀ p.1))]
  intro P
  have hbP : 0 < P.valuation F b := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hb)
  change P.valuation F ((y : F) / b) ≤ _
  rw [map_div₀, div_le_iff₀ hbP]
  by_cases hP : P ∈ S
  · let v : S := ⟨P, hP⟩
    have hxP := ((sourceFiniteBallIdeal_mem_iff F S e _).mp x.property).2 v
    change Valued.v ((x : F) : P.adicCompletion F) ≤ WithZero.exp (-(e v)) at hxP
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hxP
    have hc := sourcePrincipalExteriorModulus_count_inS F T (M p.1)
      (sourcePrimeExponentIdeal_ne_bot F S₀ p.1) (sourcePrimeExponentIdeal_exterior F S₀ p.1).2 v
    rw [hc, add_zero, ← WithZero.exp_log hbP.ne', ← WithZero.exp_add]
    change P.valuation F (x : F) ≤ _
    convert hxP using 1
    congr 1
    change (sourceDifferentExponent F P : ℤ) + WithZero.log (P.valuation F b) = -(e v)
    dsimp only [e, v]
    ring
  · have hc := sourcePrimeExponentIdeal_count_exterior F S₀ p.1 ⟨P, hP⟩
    have hdiff := (sourceDifferentExponent_eq_zero_iff F P).mpr (fun h => hP (htrace h))
    rw [hc, hdiff, Int.natCast_zero, zero_add]
    have hv : P.valuation F b = WithZero.exp (-(p.1 ⟨P, hP⟩ : ℤ)) := by
      rw [show b = (a p.1 : F) * (δ : F) from rfl, map_mul, hδS P hP, mul_one,
        sourceReducedDenominator_valuation F S₀ hζ a ha hgen p.1 ⟨P, hP⟩]
    rw [hv, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    exact y.property P hP

/-- Additive phase of the literal reduced residue on a source integer. -/
def sourceReducedFractionPhase (a : E → R) (ha : ∀ e, a e ≠ 0)
    (p : SourceReducedFractionLabel F S₀ a) (m : R) : ℂ :=
  sIntegerQuotientPhase F S (a p.1) (ha p.1) (Ideal.Quotient.mk (Ideal.span {a p.1}) m * p.2.val)

theorem sourceReducedFractionPhase_eq_lift (a : E → R) (ha : ∀ e, a e ≠ 0)
    (p : SourceReducedFractionLabel F S₀ a) (m x : R)
    (hx : Ideal.Quotient.mk (Ideal.span {a p.1}) x = (p.2 : R ⧸ Ideal.span {a p.1})) :
    sourceReducedFractionPhase F S₀ a ha p m = sCharacter F S ((m : F) * ((x : F) / (a p.1 : F))) := by
  unfold sourceReducedFractionPhase
  rw [← hx, ← map_mul (Ideal.Quotient.mk (Ideal.span {a p.1})) m x,
    sIntegerQuotientPhase_mk, Subalgebra.coe_mul, mul_div_assoc]

theorem sourceReducedFractionPhase_eq_trace (a : E → R) (ha : ∀ e, a e ≠ 0)
    (δ : 𝓞 F) (hδ : δ ≠ 0)
    (p : SourceReducedFractionLabel F S₀ a) (m x : R) (n : 𝓞 F)
    (hn : (n : F) = (m : F) * (δ : F))
    (hx : Ideal.Quotient.mk (Ideal.span {a p.1}) x = (p.2 : R ⧸ Ideal.span {a p.1}))
    (hβ : (x : F) / ((a p.1 : F) * (δ : F)) ∈ FractionalIdeal.dual ℤ ℚ (M p.1 : FI)) :
    sourceReducedFractionPhase F S₀ a ha p m =
      fieldTraceAddChar F ((x : F) / ((a p.1 : F) * (δ : F))) n := by
  let β := (x : F) / ((a p.1 : F) * (δ : F))
  have hδF : (δ : F) ≠ 0 := Subtype.coe_injective.ne hδ
  have haF : (a p.1 : F) ≠ 0 := Subtype.coe_injective.ne (ha p.1)
  have he : (m : F) * ((x : F) / (a p.1 : F)) = β * (n : F) := by
    rw [hn]
    dsimp only [β]
    field_simp
  rw [sourceReducedFractionPhase_eq_lift F S₀ a ha p m x hx, he]
  change rationalCharacter F (β * (n : F)) * (∏ P ∈ S,
    localFiniteCharacter F P (algebraMap F (P.adicCompletion F) (β * (n : F)))) = _
  have hp : (∏ P ∈ S, localFiniteCharacter F P (algebraMap F (P.adicCompletion F) (β * (n : F)))) = 1 := by
    apply Finset.prod_eq_one
    intro P hP
    apply sourceLocalCharacter_codifferent F P
    change Valued.v ((β * (n : F) : F) : P.adicCompletion F) ≤ _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_mul]
    have hβP := (sourceFractionalIdeal_dual_mem_iff F _ (FractionalIdeal.coeIdeal_ne_zero.mpr
      (sourcePrimeExponentIdeal_ne_bot F S₀ p.1)) β).mp hβ P
    have hc := sourcePrincipalExteriorModulus_count_inS F T (M p.1)
      (sourcePrimeExponentIdeal_ne_bot F S₀ p.1) (sourcePrimeExponentIdeal_exterior F S₀ p.1).2 ⟨P, hP⟩
    change FractionalIdeal.count F P (M p.1 : FI) = 0 at hc
    rw [hc, add_zero] at hβP
    exact (mul_le_mul' hβP (P.valuation_le_one n)).trans_eq (mul_one _)
  rw [hp, mul_one]
  change archCharacter F (algebraMap F (InfiniteAdeleRing F) (β * (n : F))) = _
  rw [archCharacter_rational, fieldTraceAddChar_apply]

end
end ArtinMatthews.SourcePhysical
