module

public import ArtinMatthews.FixedURootDensity
public import OAI.NumberTheory.Jacobsthal.Estimates.SourcePairRemainder
public import ArtinMatthews.FixedURootMobius
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
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.Jacobsthal.Sieve.MobiusCoprimeExpansion
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Finite progression estimates for the actual Möbius expansion in the
fixed-first-coordinate root count. -/
namespace ArtinMatthews
open OAI.Erdos970 ErdosHyperbolaError
open scoped BigOperators ArithmeticFunction.Moebius

/-- CRT with zero in the divisor coordinate and an arbitrary prescribed residue. -/
theorem fixedU_crt_residue {d S : ℕ} (hcop : d.Coprime S) (a : ℤ) :
    ∃ r : ℤ, (d : ℤ) ∣ r ∧ Int.ModEq (S : ℤ) r a := by
  obtain ⟨z,hz⟩ := Int.mod_coprime hcop
  refine ⟨(d : ℤ)*z*a,⟨z*a,by ring⟩,?_⟩
  simpa only [one_mul] using hz.mul_right a

private theorem fixedU_crt_class {d S : ℕ} (hcop : d.Coprime S)
    {a r : ℤ} (hd : (d : ℤ) ∣ r) (hr : Int.ModEq (S : ℤ) r a) (n : ℤ) :
    ((d : ℤ) ∣ n ∧ Int.ModEq (S : ℤ) n a) ↔
      Int.ModEq ((d*S : ℕ) : ℤ) n r := by
  have hm := Int.modEq_and_modEq_iff_modEq_mul
    (a := n) (b := r) (m := (d : ℤ)) (n := (S : ℤ))
    (by simpa only [Int.natAbs_natCast] using hcop)
  rw [Nat.cast_mul,← hm]
  constructor
  · rintro ⟨hdn,hn⟩
    exact ⟨hdn.modEq_zero_int.trans hd.modEq_zero_int.symm,hn.trans hr.symm⟩
  · rintro ⟨hn,hs⟩
    exact ⟨Int.modEq_zero_iff_dvd.mp (hn.trans hd.modEq_zero_int),hs.trans hr⟩

/-- One divisor term in the fixed-u density is uniformly distributed in an
arbitrary residue class, with absolute error at most one. -/
theorem fixedU_divisor_progression_count {d S : ℕ} (hd : 0 < d) (hS : 0 < S)
    (hcop : d.Coprime S) (a : ℤ) (x y : ℝ) (hxy : x ≤ y) (lc rc : Bool) :
    |(((realIntervalIntegers x y lc rc).filter
        (fun n => (d : ℤ) ∣ n ∧ Int.ModEq (S : ℤ) n a)).card : ℝ) -
      (y-x)/((d*S : ℕ) : ℝ)| ≤ 1 := by
  obtain ⟨r,hdr,hr⟩ := fixedU_crt_residue hcop a
  have he : (realIntervalIntegers x y lc rc).filter
      (fun n => (d : ℤ) ∣ n ∧ Int.ModEq (S : ℤ) n a) =
      (sourceInterval x y lc rc (d*S) r (Nat.mul_pos hd hS)).points := by
    rw [sourceInterval_points]
    apply Finset.filter_congr
    intro n _
    exact fixedU_crt_class hcop hdr hr n
  rw [he]
  exact ErdosHyperbolaFourier.progressionPoints_count_error x y hxy lc rc
    (d*S) r (Nat.mul_pos hd hS)


/-- Exact finite interchange of the divisor and progression sums. -/
theorem fixedU_divisor_sum_interchange (U : Finset ℤ) (D : Finset ℕ)
    (c : ℕ → ℝ) (S : ℕ) (a : ℤ) :
    (∑ n ∈ U.filter (fun n => Int.ModEq (S : ℤ) n a),
      ∑ d ∈ D, if (d : ℤ) ∣ n then c d else 0) =
      ∑ d ∈ D, c d * ((U.filter
        (fun n => (d : ℤ) ∣ n ∧ Int.ModEq (S : ℤ) n a)).card : ℝ) := by
  classical
  calc
    _ = ∑ n ∈ U, ∑ d ∈ D,
        if (d : ℤ) ∣ n ∧ Int.ModEq (S : ℤ) n a then c d else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : Int.ModEq (S : ℤ) n a <;> simp [hn]
    _ = ∑ d ∈ D, ∑ n ∈ U,
        if (d : ℤ) ∣ n ∧ Int.ModEq (S : ℤ) n a then c d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> simp

/-- Each actual divisor-progression count has error at most one, so the
weighted average costs only the full absolute coefficient mass. -/
theorem fixedU_finite_divisor_average (D : Finset ℕ) (c : ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d) (S : ℕ) (hS : 0 < S)
    (hcop : ∀ d ∈ D, d.Coprime S) (a : ℤ)
    (x y : ℝ) (hxy : x ≤ y) (lc rc : Bool) :
    |(∑ n ∈ (realIntervalIntegers x y lc rc).filter
        (fun n => Int.ModEq (S : ℤ) n a),
        ∑ d ∈ D, if (d : ℤ) ∣ n then c d else 0) -
      (y-x)/(S : ℝ) * ∑ d ∈ D, c d/(d : ℝ)| ≤
        ∑ d ∈ D, |c d| := by
  classical
  rw [fixedU_divisor_sum_interchange]
  have hm : (y-x)/(S : ℝ) * ∑ d ∈ D, c d/(d : ℝ) =
      ∑ d ∈ D, c d * ((y-x)/((d*S : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (hD d hd).ne'
    have hS0 : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
    push_cast
    field_simp
  rw [hm,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [← mul_sub,abs_mul]
  exact (mul_le_mul_of_nonneg_left
    (fixedU_divisor_progression_count (hD d hd) hS (hcop d hd) a x y hxy lc rc)
    (abs_nonneg _)).trans_eq (mul_one _)


/-- Divisors needed for every positive coordinate at most `N`. -/
noncomputable def fixedURootDivisors (N S : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun d => d.Coprime S

theorem fixedURootDensity_eq_truncated {u N S : ℕ} (hu : 0 < u) (huN : u ≤ N) :
    fixedURootDensity u (Nat.gcd S u) =
      ∑ d ∈ fixedURootDivisors N S, if d ∣ u then (μ d : ℝ)/(d : ℝ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  have he : (fixedURootDivisors N S).filter (fun d => d ∣ u) =
      u.divisors.filter (fun d => d.Coprime S) := by
    ext d
    constructor
    · intro hd
      obtain ⟨hdD,hdu⟩ := Finset.mem_filter.mp hd
      obtain ⟨_,hcop⟩ := Finset.mem_filter.mp hdD
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdu,hu.ne'⟩,hcop⟩
    · intro hd
      obtain ⟨hdU,hcop⟩ := Finset.mem_filter.mp hd
      have hdu := Nat.dvd_of_mem_divisors hdU
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_,hcop⟩,hdu⟩
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdU,
        (Nat.le_of_dvd hu hdu).trans huN⟩
  rw [he]
  exact fixedURootDensity_eq_moebius_sum hu

/-- The complete absolute coefficient mass is bounded by a harmonic sum. -/
theorem fixedURootDivisors_moebius_mass (N S : ℕ) :
    (∑ d ∈ fixedURootDivisors N S, |(μ d : ℝ)/(d : ℝ)|) ≤ 1+Real.log N := by
  classical
  calc
    _ ≤ ∑ d ∈ fixedURootDivisors N S, (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_div,abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d)]
      exact (div_le_div_of_nonneg_right
        (ErdosCoprimeResidueInterval.moebius_abs_le_one d) (Nat.cast_nonneg d)).trans_eq
          (one_div _)
    _ ≤ ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
    _ = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log N

private theorem fixedU_interval_bounds {x y : ℝ} {lc rc : Bool} {n : ℤ}
    (hn : n ∈ realIntervalIntegers x y lc rc) : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ y := by
  obtain ⟨_,hl,hr⟩ := Finset.mem_filter.mp hn
  constructor
  · cases lc
    · exact le_of_lt hl
    · exact hl
  · cases rc
    · exact le_of_lt hr
    · exact hr

/-- Averaging the actual Euler density along any progression has logarithmic
error, with the genuine truncated reciprocal-square Möbius main coefficient. -/
theorem fixedURootDensity_progression_average (N S : ℕ) (hS : 0 < S) (a : ℤ)
    (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N) (lc rc : Bool) :
    |(∑ n ∈ (realIntervalIntegers x y lc rc).filter
        (fun n => Int.ModEq (S : ℤ) n a),
        fixedURootDensity n.natAbs (Nat.gcd S n.natAbs)) -
      (y-x)/(S : ℝ) *
        (∑ d ∈ fixedURootDivisors N S, (μ d : ℝ)/(d : ℝ)^2)| ≤
      1+Real.log N := by
  classical
  have hdpos : ∀ d ∈ fixedURootDivisors N S, 0 < d := by
    intro d hd
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  have hdcop : ∀ d ∈ fixedURootDivisors N S, d.Coprime S := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  have hh := fixedU_finite_divisor_average (fixedURootDivisors N S)
    (fun d => (μ d : ℝ)/(d : ℝ)) hdpos S hS hdcop a x y hxy lc rc
  have hpoint (n : ℤ) (hn : n ∈ realIntervalIntegers x y lc rc) :
      fixedURootDensity n.natAbs (Nat.gcd S n.natAbs) =
        ∑ d ∈ fixedURootDivisors N S,
          if (d : ℤ) ∣ n then (μ d : ℝ)/(d : ℝ) else 0 := by
    obtain ⟨hxn,hny⟩ := fixedU_interval_bounds hn
    have hnZ : 0 < n := by exact_mod_cast (lt_of_lt_of_le (by linarith : (0:ℝ)<x) hxn)
    have hncast : (n.natAbs : ℤ) = n := by
      rw [Int.natCast_natAbs,abs_of_nonneg hnZ.le]
    have hncastR : (n.natAbs : ℝ) = (n : ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hncast
    have hnpos : 0 < n.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnZ)
    have hnN : n.natAbs ≤ N := by
      exact_mod_cast (show (n.natAbs : ℝ) ≤ N by rw [hncastR]; exact hny.trans hyN)
    simpa only [Int.natCast_dvd] using fixedURootDensity_eq_truncated (S := S) hnpos hnN
  have hsum : (∑ n ∈ (realIntervalIntegers x y lc rc).filter
      (fun n => Int.ModEq (S : ℤ) n a),
      fixedURootDensity n.natAbs (Nat.gcd S n.natAbs)) =
      ∑ n ∈ (realIntervalIntegers x y lc rc).filter
        (fun n => Int.ModEq (S : ℤ) n a),
        ∑ d ∈ fixedURootDivisors N S,
          if (d : ℤ) ∣ n then (μ d : ℝ)/(d : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n (Finset.mem_filter.mp hn).1
  rw [hsum]
  have hmain : (∑ d ∈ fixedURootDivisors N S, (μ d : ℝ)/(d : ℝ)^2) =
      ∑ d ∈ fixedURootDivisors N S, ((μ d : ℝ)/(d : ℝ))/(d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [div_div,pow_two]
  rw [hmain]
  exact hh.trans (fixedURootDivisors_moebius_mass N S)

end ArtinMatthews
