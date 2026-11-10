module

public import ArtinMatthews.SIntegerStandardPhase
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

/-! The CFT normalized finite-place value of a global field unit is
the logarithm of the actual adic valuation. This extends the pinned
integral-element comparison by genuine fraction decomposition. -/
namespace ArtinMatthews.SIntegerAllowedReciprocity

open NumberField IsDedekindDomain KummerTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open GlobalClassFieldTheory.Reciprocity
open ArtinMatthews.SIntegerPrincipalization ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical ValuativeRel nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem normalizedValue_div (P : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    finitePlaceNormalizedValuation K P (a / b) =
      finitePlaceNormalizedValuation K P a - finitePlaceNormalizedValuation K P b := by
  let C := (HeightOneSpectrum.adicAbv K P).Completion
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel P
  let : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField P
  change valuationMap C (Additive.ofMul (finitePlaceHilbert_completionUnit K P (a / b))) =
    valuationMap C (Additive.ofMul (finitePlaceHilbert_completionUnit K P a)) -
      valuationMap C (Additive.ofMul (finitePlaceHilbert_completionUnit K P b))
  simp only [finitePlaceHilbert_completionUnit, map_div, valuationMap_ofMul_div]

theorem normalizedValue_integral_eq_log (P : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ≠ 0) :
    finitePlaceNormalizedValuation K P (nonzeroIntegralFieldUnit K a ha) =
      WithZero.log (P.valuation K (a : K)) := by
  rw [finitePlaceNormalizedValuation_nonzeroIntegralFieldUnit, P.valuation_of_algebraMap,
    intValuation_eq_exp_neg_idealPrimeMultiplicity K P a ha, WithZero.log_exp]

theorem normalizedValue_eq_log (P : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    finitePlaceNormalizedValuation K P x = WithZero.log (P.valuation K (x : K)) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro he
    apply x.ne_zero
    rw [← hab, he, map_zero, zero_div]
  let u := nonzeroIntegralFieldUnit K a ha0
  let v := nonzeroIntegralFieldUnit K b hb0
  have hx : x = u / v := by
    apply Units.ext
    rw [Units.val_div_eq_div_val]
    exact hab.symm
  rw [hx, normalizedValue_div K P u v,
    normalizedValue_integral_eq_log K P a ha0, normalizedValue_integral_eq_log K P b hb0]
  simp only [Units.val_div_eq_div_val, u, v, nonzeroIntegralFieldUnit_coe]
  rw [map_div₀, WithZero.log_div]
  · exact (Valuation.ne_zero_iff _).mpr ((IsFractionRing.injective (𝓞 K) K).ne ha0)
  · exact (Valuation.ne_zero_iff _).mpr ((IsFractionRing.injective (𝓞 K) K).ne hb0)

theorem normalizedValue_generator (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    finitePlaceNormalizedValuation K P (generatorFieldUnit S₀ P a ha) = -1 := by
  rw [normalizedValue_eq_log K P, generatorFieldUnit_valuation S₀ P hP a ha, WithZero.log_exp]

end
end ArtinMatthews.SIntegerAllowedReciprocity
