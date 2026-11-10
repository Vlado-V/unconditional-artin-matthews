module

public import ArtinMatthews.ProbeIdealPrimeFourier
public import ArtinMatthews.StandardAdelicLocalNontrivial
public import ArtinMatthews.StandardAdelicLocalQuotient
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal standard phase attached to any actual local prime
element, including a field-valued S-integer prime generator. Its
comparison multiplier with the frozen tower is derived, not supplied. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem choicePrime_pow_valuation (P : HeightOneSpectrum (𝓞 K)) (u : P.adicCompletion K)
    (hu : (Valued.v : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
    (n : ℕ) : Valued.v (u ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [map_pow, hu, ← WithZero.exp_nsmul]
  congr 1
  simp

def choiceIntegerPhase (P : HeightOneSpectrum (𝓞 K)) (u : P.adicCompletion K) (n : ℕ) : AddChar (𝓞 K) ℂ where
  toFun x := localFiniteCharacter K P (-(algebraMap (𝓞 K) (P.adicCompletion K) x) / u ^ n)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [map_add, neg_add, add_div, AddChar.map_add_eq_mul]

theorem choiceIntegerPhase_period (P : HeightOneSpectrum (𝓞 K)) (u : P.adicCompletion K)
    (hu : (Valued.v : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
    (n : ℕ) (x : 𝓞 K) (hx : x ∈ P.asIdeal ^ n) : choiceIntegerPhase K P u n x = 1 := by
  apply localFiniteCharacter_integral
  change Valued.v (-(algebraMap (𝓞 K) (P.adicCompletion K) x) / u^n) ≤ 1
  rw [map_div₀, Valuation.map_neg, choicePrime_pow_valuation K P u hu, localInteger_valuation]
  exact (div_le_one₀ (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)).mpr
    ((P.intValuation_le_pow_iff_mem x n).mpr hx)

def choiceQuotientPhase (P : HeightOneSpectrum (𝓞 K)) (u : P.adicCompletion K)
    (hu : (Valued.v : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
    (n : ℕ) : AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift (P.asIdeal ^ n).toAddSubgroup
    (choiceIntegerPhase K P u n).toAddMonoidHom (fun x hx => choiceIntegerPhase_period K P u hu n x hx))

theorem choiceQuotientPhase_mk (P : HeightOneSpectrum (𝓞 K)) (u : P.adicCompletion K)
    (hu : (Valued.v : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
    (n : ℕ) (x : 𝓞 K) : choiceQuotientPhase K P u hu n (Ideal.Quotient.mk _ x) =
      localFiniteCharacter K P (-(algebraMap (𝓞 K) (P.adicCompletion K) x) / u ^ n) := rfl

theorem choiceQuotientPhase_primitive (P : HeightOneSpectrum (𝓞 K)) (u : P.adicCompletion K)
    (hu : (Valued.v : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
    (n : ℕ) (hP : P ∉ traceBadPlaces K) : (choiceQuotientPhase K P u hu n).IsPrimitive := by
  intro a ha hshift
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  apply ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  let c := -(algebraMap (𝓞 K) (P.adicCompletion K) a) / u ^ n
  have hc : c ∈ P.adicCompletionIntegers K := (localFiniteCharacter_integer_dual K P hP c).mp (by
    intro b
    have h := congrArg (fun χ : AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ => χ (Ideal.Quotient.mk _ b)) hshift
    change choiceQuotientPhase K P u hu n ((Ideal.Quotient.mk _ a) * (Ideal.Quotient.mk _ b)) = 1 at h
    rw [← map_mul (Ideal.Quotient.mk (P.asIdeal ^ n)) a b, choiceQuotientPhase_mk] at h
    change localFiniteCharacter K P (c * algebraMap (𝓞 K) (P.adicCompletion K) b) = 1
    convert h using 1
    congr 1
    dsimp only [c]
    rw [map_mul]
    ring)
  change Valued.v c ≤ 1 at hc
  dsimp only [c] at hc
  rw [map_div₀, Valuation.map_neg, choicePrime_pow_valuation K P u hu, localInteger_valuation] at hc
  exact (P.intValuation_le_pow_iff_mem a n).mp
    ((div_le_one₀ (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)).mp hc)

theorem choiceQuotientPhase_comparison_exists (P : HeightOneSpectrum (𝓞 K)) (u : P.adicCompletion K)
    (hu : (Valued.v : Valuation (P.adicCompletion K) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
    (n : ℕ) (hP : P ∉ traceBadPlaces K) :
    ∃ b : ((𝓞 K) ⧸ P.asIdeal ^ n)ˣ,
      (probeIdealPhase K P n).mulShift (b : _) = choiceQuotientPhase K P u hu n := by
  let : Finite ((𝓞 K) ⧸ P.asIdeal ^ n) := Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero n P.ne_bot)
  let : Fintype ((𝓞 K) ⧸ P.asIdeal ^ n) := Fintype.ofFinite _
  exact probe_addChar_exists_unit_shift _ _ (probeIdealPhase_primitive K P n) (choiceQuotientPhase_primitive K P u hu n hP)

def generatorPhase (P : HeightOneSpectrum (𝓞 K)) (p : Kˣ)
    (hp : P.valuation K (p : K) = WithZero.exp (-1 : ℤ)) (n : ℕ) : AddChar ((𝓞 K) ⧸ P.asIdeal ^ n) ℂ :=
  choiceQuotientPhase K P (algebraMap K (P.adicCompletion K) (p : K))
    (by change Valued.v ((p : K) : P.adicCompletion K) = _
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hp) n

theorem generatorPhase_mk (P : HeightOneSpectrum (𝓞 K)) (p : Kˣ)
    (hp : P.valuation K (p : K) = WithZero.exp (-1 : ℤ)) (n : ℕ) (x : 𝓞 K) :
    generatorPhase K P p hp n (Ideal.Quotient.mk _ x) =
      localFiniteCharacter K P (-(algebraMap K (P.adicCompletion K) ((x : K)/(p : K)^n))) := by
  rw [generatorPhase, choiceQuotientPhase_mk]
  congr 1
  rw [map_div₀, map_pow,
    ← IsScalarTower.algebraMap_apply (𝓞 K) K (P.adicCompletion K), neg_div]

theorem generatorPhase_primitive (P : HeightOneSpectrum (𝓞 K)) (p : Kˣ)
    (hp : P.valuation K (p : K) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (hP : P ∉ traceBadPlaces K) : (generatorPhase K P p hp n).IsPrimitive :=
  choiceQuotientPhase_primitive K P _ _ n hP

theorem generatorPhase_comparison_exists (P : HeightOneSpectrum (𝓞 K)) (p : Kˣ)
    (hp : P.valuation K (p : K) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (hP : P ∉ traceBadPlaces K) :
    ∃ b : ((𝓞 K) ⧸ P.asIdeal ^ n)ˣ,
      (probeIdealPhase K P n).mulShift (b : _) = generatorPhase K P p hp n :=
  choiceQuotientPhase_comparison_exists K P _ _ n hP

end
end ArtinMatthews.StandardAdelic
