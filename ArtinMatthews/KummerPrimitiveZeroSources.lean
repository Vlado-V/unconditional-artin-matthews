module

public import ArtinMatthews.ArtinPrimitiveZeroSources
public import ArtinMatthews.KummerCyclotomicTower
public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
public import ArtinMatthews.KummerCyclotomicTowerAbelian
public import ArtinMatthews.KummerCyclotomicTowerComplex
public import ArtinMatthews.KummerOriginalComplex
public import ArtinMatthews.KummerPrimitiveNonreal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual zero-source reduction for K_q=Q(mu_q,a^(1/q)).
The principal cyclotomic factor is retained. All other sources are
non-real primitive Hecke factors over Q(mu_12q), with explicit q-dependent
conductor bounds. This does not assert the fixed-width zero-free theorem. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain
open scoped NumberField Classical IsMulCommutative
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem PrimitiveArtinZeroWitness.log_conductor_le {s : ℂ}
    (w : PrimitiveArtinZeroWitness K L s) :
    Real.log (w.conductor.absNorm : ℝ) ≤
      (Module.finrank ℚ K : ℝ) * Real.log (discriminantDegreeModulus K L : ℝ) := by
  have hfpos : 0 < (w.conductor.absNorm : ℝ) := by
    exact_mod_cast (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr w.conductor_ne_zero))
  have hN := w.norm_le
  rw [rationalModulusIdeal, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at hN
  have hr : (w.conductor.absNorm : ℝ) ≤
      (discriminantDegreeModulus K L : ℝ) ^ Module.finrank ℚ K := by exact_mod_cast hN
  have hlog := Real.log_le_log hfpos hr
  rwa [Real.log_pow] at hlog

theorem PrimitiveArtinZeroWitness.ne_one {s : ℂ} (w : PrimitiveArtinZeroWitness K L s) : s ≠ 1 := by
  intro he
  exact w.one_ne_zero (he ▸ w.zero)

theorem mixedCompletedDedekindXi_zero_regularized (K : Type) [Field K] [NumberField K]
    {s : ℂ} (hs : mixedCompletedDedekindXi K s = 0) : mixedRegularizedDedekindZeta K s = 0 := by
  simp only [mixedRegularizedDedekindZeta, hs, zero_mul, zero_div]

theorem primeKummer_regularized_zero_sources (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hq : 2 < q) {s : ℂ} (hs : 0 < s.re)
    (hz : mixedRegularizedDedekindZeta (primeKummerField q a) s = 0) :
    mixedRegularizedDedekindZeta (twelfthCyclotomicField q) s = 0 ∨
      Nonempty (PrimitiveArtinZeroWitness (twelfthCyclotomicField q) (twelfthKummerField q a) s) := by
  let := primeKummerField_isTotallyComplex q a hq
  have htop := ArtinRay.regularizedDedekindZeta_base_zero
    (primeKummerField q a) (twelfthKummerField q a) hs hz
  exact (ArtinRay.regularizedDedekindZeta_zero_sources
    (twelfthCyclotomicField q) (twelfthKummerField q a) hs).mp htop

theorem twelfthKummer_primitive_zero_source_log_conductor
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] (haq : a.natAbs ≤ q) {s : ℂ}
    (w : PrimitiveArtinZeroWitness (twelfthCyclotomicField q) (twelfthKummerField q a) s) :
    Real.log (w.conductor.absNorm : ℝ) ≤
      (12 * q : ℝ) * ((72 * (q : ℝ)^2 + 2) * Real.log (12 * q)) := by
  have hdim : (Module.finrank ℚ (twelfthCyclotomicField q) : ℝ) ≤ (12 * q : ℝ) := by
    rw [finrank_twelfthCyclotomicField]
    exact_mod_cast Nat.totient_le (12 * q)
  have hlog := twelfthKummer_cyclotomic_discriminantDegreeModulus_log_le q a haq
  have hB : 0 ≤ (72 * (q : ℝ)^2 + 2) * Real.log (12 * q) := by
    have hq0 := NeZero.pos q
    have : (1 : ℝ) ≤ 12 * q := by exact_mod_cast (show 1 ≤ 12 * q by omega)
    exact mul_nonneg (by positivity) (Real.log_nonneg this)
  exact w.log_conductor_le.trans
    ((mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hdim hB))

theorem primeKummer_xi_zero_sources (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hq : 2 < q) (hodd : Odd q) (haq : a.natAbs ≤ q) {s : ℂ} (hs : 0 < s.re)
    (hz : mixedCompletedDedekindXi (primeKummerField q a) s = 0) :
    mixedRegularizedDedekindZeta (twelfthCyclotomicField q) s = 0 ∨
      ∃ w : PrimitiveArtinZeroWitness (twelfthCyclotomicField q) (twelfthKummerField q a) s,
        w.primitiveCharacter.coefficient ≠ w.primitiveCharacter.inverse.coefficient ∧
        (∃ I, (w.primitiveCharacter.coefficient I).im ≠ 0) ∧
        Real.log (w.conductor.absNorm : ℝ) ≤
          (12 * q : ℝ) * ((72 * (q : ℝ)^2 + 2) * Real.log (12 * q)) := by
  rcases primeKummer_regularized_zero_sources q a hq hs
    (mixedCompletedDedekindXi_zero_regularized _ hz) with hbase | hw
  · exact Or.inl hbase
  · obtain ⟨w⟩ := hw
    exact Or.inr ⟨w, (twelfthKummer_primitive_zero_source_nonreal q a hodd w).1,
      (twelfthKummer_primitive_zero_source_nonreal q a hodd w).2,
      twelfthKummer_primitive_zero_source_log_conductor q a haq w⟩


theorem primeKummer_prime_xi_zero_sources (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hprime : q.Prime) (hq : 2 < q) (haq : a.natAbs ≤ q) {s : ℂ} (hs : 0 < s.re)
    (hz : mixedCompletedDedekindXi (primeKummerField q a) s = 0) :
    mixedRegularizedDedekindZeta (twelfthCyclotomicField q) s = 0 ∨
      ∃ w : PrimitiveArtinZeroWitness (twelfthCyclotomicField q) (twelfthKummerField q a) s,
        w.primitiveCharacter.coefficient ≠ w.primitiveCharacter.inverse.coefficient ∧
        (∃ I, (w.primitiveCharacter.coefficient I).im ≠ 0) ∧
        Real.log (w.conductor.absNorm : ℝ) ≤
          (12 * q : ℝ) * ((72 * (q : ℝ)^2 + 2) * Real.log (12 * q)) :=
  primeKummer_xi_zero_sources q a hq (hprime.odd_of_ne_two (by omega)) haq hs hz

end
end ArtinMatthews.VaryingKummerAnalytic
