module

public import ArtinMatthews.VaryingKummerAnalyticRayCharacter
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Henselian
public import ArtinMatthews.ArtinRayLocalCongruence
public import ArtinMatthews.HenselPowerNorm
public import ArtinMatthews.HenselPowerUnits
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
public import Mathlib.Topology.Sheaves.Init
public import ValuedFieldTheory.Valuation.ValuedAdicComplete


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative power lifting in the actual finite-place completions. -/
noncomputable section
open scoped NumberField
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay

variable {K : Type*} [Field K] [NumberField K]

theorem completedIntegers_henselianLocalRing
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    HenselianLocalRing (v.adicCompletionIntegers K) := by
  let : IsAdicComplete
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
    ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete
  refine { is_henselian := ?_ }
  intro f hf a ha hder
  exact HenselianRing.is_henselian f hf a ha
    (hder.map (Ideal.Quotient.mk _))

theorem completed_congruence_degreeSquare
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (D n : ℕ)
    {a : 𝓞 K} (ha : a - 1 ∈ rationalModulusIdeal (𝓞 K) (D * n^2)) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      Ideal.span {((D : v.adicCompletionIntegers K) *
        (n : v.adicCompletionIntegers K)^2)} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  apply Ideal.mem_span_singleton.mpr
  refine ⟨algebraMap (𝓞 K) (v.adicCompletionIntegers K) b, ?_⟩
  rw [← map_one (algebraMap (𝓞 K) (v.adicCompletionIntegers K)), ← map_sub, hb]
  simp only [map_mul, map_natCast, Nat.cast_mul, Nat.cast_pow, map_pow]

/-- A principal generator congruent to one modulo `D*n²` has an actual
`n`-th root among local integer units at every prime dividing `D`. -/
theorem completed_principal_exists_unit_pow
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (D n : ℕ) (hn : 0 < n)
    (hD : (D : 𝓞 K) ∈ v.asIdeal) {a : 𝓞 K}
    (ha : a - 1 ∈ rationalModulusIdeal (𝓞 K) (D * n^2)) :
    ∃ w : (v.adicCompletionIntegers K)ˣ,
      (w : v.adicCompletionIntegers K)^n =
        algebraMap (𝓞 K) (v.adicCompletionIntegers K) a := by
  let := completedIntegers_henselianLocalRing v
  have hDm : (D : v.adicCompletionIntegers K) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    simpa only [map_natCast] using integral_mem_completed_maximal v hD
  have hc := completed_congruence_degreeSquare v D n ha
  have hsub : algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hc
    rw [hb]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hDm)
  have hu := completed_integral_isUnit_of_congruence v (by decide : 0 < 1)
    (by simpa only [pow_one] using hsub)
  have hc' : (hu.unit : v.adicCompletionIntegers K) - 1 ∈
      Ideal.span {((D : v.adicCompletionIntegers K) *
        (n : v.adicCompletionIntegers K)^2)} := by
    rwa [hu.unit_spec]
  have hp : (hu.unit : v.adicCompletionIntegers K) - 1 ∈
      Ideal.span {(n : v.adicCompletionIntegers K)^2} *
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hc'
    rw [hb, show (D : v.adicCompletionIntegers K) * n^2 * b = n^2 * (D*b) by ring]
    exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton _))
      (Ideal.mul_mem_right _ _ hDm)
  obtain ⟨w, hw⟩ := HenselPower.exists_unit_pow_of_sub_one_mem n hn hu.unit hp
  refine ⟨w, ?_⟩
  simpa only [Units.val_pow_eq_pow_val, hu.unit_spec] using congrArg Units.val hw

/-- The same explicit rational congruence is a genuine norm in every
finite extension of the actual completion whose degree divides `n`. -/
theorem completed_principal_exists_unit_norm
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (L : Type*) [Field L] [Algebra (v.adicCompletion K) L]
    [FiniteDimensional (v.adicCompletion K) L]
    (D n : ℕ) (hn : 0 < n) (hd : Module.finrank (v.adicCompletion K) L ∣ n)
    (hD : (D : 𝓞 K) ∈ v.asIdeal) {a : 𝓞 K}
    (ha : a - 1 ∈ rationalModulusIdeal (𝓞 K) (D * n^2)) :
    ∃ w : Lˣ, Algebra.norm (v.adicCompletion K) (w : L) =
      algebraMap K (v.adicCompletion K) (a : K) := by
  obtain ⟨r, hr⟩ := completed_principal_exists_unit_pow v D n hn hD ha
  obtain ⟨w, hw⟩ := HenselPower.exists_unit_norm_of_pow
    (K := v.adicCompletion K) (L := L) n hd (r^n) r rfl
  refine ⟨w, ?_⟩
  have h := congrArg Units.val hw
  simp only [Units.coe_map, Units.val_pow_eq_pow_val] at h
  rw [hr] at h
  exact h

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
