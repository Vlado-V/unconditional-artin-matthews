module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import ArtinMatthews.VaryingKummerAnalyticRayFractionalDenominator
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.Henselian
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

/-! The exact prime-factor count hypothesis implies actual local-unit
membership, hence genuine coprime integral numerator and denominator. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem ray_valuation_eq_one_of_count_zero (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ)
    (hc : FractionalIdeal.count K v (spanSingleton (𝓞 K)⁰ (x : K)) = 0) :
    v.valuation K (x : K) = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_nonzero_integral_fraction K x
  have hs : spanSingleton (𝓞 K)⁰ (x : K) =
      spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K b)⁻¹) *
        ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, hab]
    congr 1
    exact div_eq_inv_mul _ _
  have H := FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero) hs
  rw [hc] at H
  have he : (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors =
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors := by
    exact_mod_cast (sub_eq_zero.mp H.symm)
  rw [hab, map_div₀, v.valuation_of_algebraMap a, v.valuation_of_algebraMap b,
    v.intValuation_if_neg ha, v.intValuation_if_neg hb, he]
  exact div_self WithZero.exp_ne_zero

theorem exists_coprime_integral_fraction_of_counts
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (x : Kˣ)
    (hlocal : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ M →
      FractionalIdeal.count K v (spanSingleton (𝓞 K)⁰ (x : K)) = 0) :
    ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ IsCoprime (Ideal.span {a}) M ∧
      IsCoprime (Ideal.span {b}) M ∧ (x : K) = (a : K) / (b : K) :=
  exists_coprime_integral_fraction_of_local_units K M hM x
    (fun v hv => ray_valuation_eq_one_of_count_zero K v x (hlocal v hv))

end
end ArtinMatthews.VaryingKummerAnalytic
