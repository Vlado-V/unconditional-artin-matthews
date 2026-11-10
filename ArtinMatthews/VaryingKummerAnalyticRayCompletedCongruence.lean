module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact pullback of completed prime-power congruences and fractional
higher-unit congruences to the ring of integers. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem completed_integral_mem_prime_pow_iff
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (a : 𝓞 K) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) a ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)^n ↔ a ∈ v.asIdeal^n := by
  let f := algebraMap (𝓞 K) (v.adicCompletionIntegers K)
  have hval (r : 𝓞 K) :
      Valued.v ((f r : v.adicCompletionIntegers K) : v.adicCompletion K) = v.intValuation r := by
    change Valued.v (((algebraMap (𝓞 K) K r):K):v.adicCompletion K) = v.intValuation r
    rw [v.valuedAdicCompletion_eq_valuation',v.valuation_of_algebraMap]
  constructor
  · intro ha
    obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
    have hlt := (HeightOneSpectrum.adicCompletionIntegers.integers K v).valuation_irreducible_lt_one hπ
    have hp0 := (HeightOneSpectrum.adicCompletionIntegers.integers K v).valuation_irreducible_pos hπ
    change Valued.v (π:v.adicCompletion K) < 1 at hlt
    change 0 < Valued.v (π:v.adicCompletion K) at hp0
    have hp : Valued.v (π : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) := by
      have hlog : WithZero.log (Valued.v (π : v.adicCompletion K)) < 0 := by
        rwa [← WithZero.exp_log hp0.ne',WithZero.exp_lt_one_iff] at hlt
      rw [← WithZero.exp_log hp0.ne',WithZero.exp_le_exp]
      omega
    have hmem := (HeightOneSpectrum.adicCompletionIntegers.integers K v).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hπ n
    have hbound : Valued.v ((f a : v.adicCompletionIntegers K) : v.adicCompletion K) ≤
        (Valued.v (π : v.adicCompletion K))^n := by
      exact (Set.ext_iff.mp hmem (f a)).mp ha
    apply (v.intValuation_le_pow_iff_mem a n).mp
    rw [← hval a]
    apply hbound.trans
    calc
      (Valued.v (π : v.adicCompletion K))^n ≤ (WithZero.exp (-1 : ℤ))^n :=
        pow_le_pow_left₀ zero_le hp n
      _ = WithZero.exp (-(n:ℤ)) := by simp [← WithZero.exp_nsmul]
  · intro ha
    have hmap : Ideal.map f v.asIdeal ≤ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      apply (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).mpr
      change Valued.v ((f b : v.adicCompletionIntegers K) : v.adicCompletion K) < 1
      rw [hval b]
      exact (v.intValuation_lt_one_iff_mem b).mpr hb
    have hm : Ideal.map f (v.asIdeal^n) ≤
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)^n := by
      rw [Ideal.map_pow]
      gcongr
    exact hm (Ideal.mem_map_of_mem f ha)

theorem principal_local_higherUnit_valuation_one
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : Kˣ)
    (hx : (IdeleGroup.principalIdele K x).2 v ∈ localHigherUnitGroup v n) :
    v.valuation K (x:K) = 1 := by
  have h := (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mp
    (localHigherUnitGroup_le_integralUnits v n hx)
  change Valued.v ((x:K):v.adicCompletion K) = 1 at h
  rwa [v.valuedAdicCompletion_eq_valuation'] at h

theorem principal_local_higherUnit_integral_difference
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : Kˣ)
    (hx : (IdeleGroup.principalIdele K x).2 v ∈ localHigherUnitGroup v n)
    (a b : 𝓞 K) (hab : (b:K)*(x:K)=(a:K)) : a-b ∈ v.asIdeal^n := by
  obtain ⟨y,hy,hy1⟩ := (mem_localHigherUnitGroup_iff v n _).mp hx
  have hcong := (localHigherUnitMap_eq_one_iff v n y).mp hy1
  let f := algebraMap (𝓞 K) (v.adicCompletionIntegers K)
  have he : f b * localIntegralValue v y = f a := by
    apply Subtype.ext
    have hv := congrArg (fun z : (v.adicCompletion K)ˣ => (z:v.adicCompletion K)) hy
    change ((localIntegralValue v y : v.adicCompletionIntegers K):v.adicCompletion K) =
      ((x:K):v.adicCompletion K) at hv
    change ((b:K):v.adicCompletion K) *
      ((localIntegralValue v y : v.adicCompletionIntegers K):v.adicCompletion K) =
        ((a:K):v.adicCompletion K)
    rw [hv,← HeightOneSpectrum.adicCompletion.coe_mul,hab]
  apply (completed_integral_mem_prime_pow_iff v n (a-b)).mp
  have H := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)^n).mul_mem_left (f b) hcong
  simpa only [map_sub,mul_sub,mul_one,he] using H

end
end ArtinMatthews.VaryingKummerAnalytic
