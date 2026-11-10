module

public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencyCoordinates
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencySeparation
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualNormIdeal
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

/-! Actual rational trace-dual frequencies for the scaled integral-basis cusp lattice. -/
namespace ArtinMatthews
open NumberField Module Module.Free
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

def sourceKPCuspTraceFrequency (n : I → ℤ) : K :=
  (d : K)⁻¹ * idealTraceIntegerLift K n

include hd in
theorem sourceKPCuspTraceFrequency_pair (n : I → ℤ) (i : I) :
    (Algebra.trace ℚ K (sourceKPCuspTraceFrequency K d n * ((d : K) * integralBasis K i)) : ℝ) =
      (n i : ℝ) := by
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have he : sourceKPCuspTraceFrequency K d n * ((d : K) * integralBasis K i) =
      idealTraceIntegerLift K n * integralBasis K i := by
    unfold sourceKPCuspTraceFrequency
    field_simp
  rw [he]
  exact congrFun (idealTraceIntegerLift_coordinates K n) i

include hd in
theorem sourceKPCuspTraceFrequency_ne_zero {n : I → ℤ} (hn : n ≠ 0) :
    sourceKPCuspTraceFrequency K d n ≠ 0 := by
  intro he
  apply hn
  ext i
  have h := sourceKPCuspTraceFrequency_pair K d hd n i
  rw [he, zero_mul, map_zero, Rat.cast_zero] at h
  change n i = 0
  exact_mod_cast h.symm

theorem sourceKPCuspTraceFrequency_mem_dual (n : I → ℤ) :
    sourceKPCuspTraceFrequency K d n ∈
      FractionalIdeal.dual ℤ ℚ ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.dual_eq_mul_inv, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv]
  have h := FractionalIdeal.mul_mem_mul (idealTraceIntegerLift_mem_dual K n)
    (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ ((d : K)⁻¹))
  simpa only [sourceKPCuspTraceFrequency, mul_comm (d : K)⁻¹ (idealTraceIntegerLift K n)] using h

theorem sourceKPCuspTraceFrequency_dualIdeal :
    FractionalIdeal.dual ℤ ℚ ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ ((d : K)⁻¹) := by
  rw [FractionalIdeal.dual_eq_mul_inv, coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv,
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv]

include hd in
theorem sourceKPCuspTraceFrequency_norm_lower {n : I → ℤ} (hn : n ≠ 0) :
    1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm (Ideal.span {d}) : ℝ)) ≤
      |(Algebra.norm ℚ (sourceKPCuspTraceFrequency K d n) : ℝ)| := by
  have hM : (Ideal.span {d} : Ideal (𝓞 K)) ≠ ⊥ := by simpa using hd
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0
    ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hM)
  have h := fractionalIdeal_absNorm_le_element_norm K (mixedTraceDualIdeal K J)
    (sourceKPCuspTraceFrequency_ne_zero K d hd hn) (sourceKPCuspTraceFrequency_mem_dual K d n)
  rw [mixedTraceDualIdeal_absNorm_div] at h
  simpa only [J, Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] using h

include hd in
theorem sourceKPCuspTraceFrequency_embedding_ne_zero {n : I → ℤ} (hn : n ≠ 0)
    (v : InfinitePlace K) : v.embedding (sourceKPCuspTraceFrequency K d n) ≠ 0 :=
  (map_ne_zero v.embedding).mpr (sourceKPCuspTraceFrequency_ne_zero K d hd hn)

include hd in
theorem sourceKPCuspTraceFrequency_product_lower [IsTotallyComplex K]
    {n : I → ℤ} (hn : n ≠ 0) :
    1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm (Ideal.span {d}) : ℝ)) ≤
      ∏ v : InfinitePlace K, ‖v.embedding (sourceKPCuspTraceFrequency K d n)‖ ^ 2 := by
  have h := sourceKPCuspTraceFrequency_norm_lower K d hd hn
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm] at h
  simpa only [IsTotallyComplex.mult_eq, InfinitePlace.norm_embedding_eq] using h

end
end ArtinMatthews
