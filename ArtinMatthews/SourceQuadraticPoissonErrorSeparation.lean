module

public import ArtinMatthews.QuadraticHeckeFiniteEnergy
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Exact separation of the annular column norm factors on a positive
Mellin line. All identities preserve the conjugation on the first
coefficient. -/

namespace ArtinMatthews
open Complex MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem quadraticPoisson_sqrt_cpow {q : ℝ} (hq : 0 ≤ q) (s : ℂ) :
    (Real.sqrt q : ℂ) ^ s = (q : ℂ) ^ (s / 2) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Complex.cpow_mul_ofReal_nonneg hq (1 / 2 : ℝ) s]
  congr 1
  push_cast
  ring

theorem quadraticPoisson_sqrt_cpow_div {q : ℝ} (hq : 0 < q) (s : ℂ) :
    (Real.sqrt q : ℂ) ^ s / (Real.sqrt q : ℂ) = (q : ℂ) ^ ((s - 1) / 2) := by
  rw [← quadraticPoisson_sqrt_cpow hq.le (s - 1),
    Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq).ne'),
    Complex.cpow_one]

theorem quadraticPoisson_sqrt_pair_normalize {R b c : ℝ}
    (hR : 0 < R) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (b * c) = R * (Real.sqrt (b / R) * Real.sqrt (c / R)) := by
  rw [← Real.sqrt_mul (div_pos hb hR).le]
  have hratio : b / R * (c / R) = b * c / R ^ 2 := by field_simp
  rw [hratio, Real.sqrt_div (mul_pos hb hc).le, Real.sqrt_sq hR.le]
  field_simp

theorem quadraticPoisson_normalized_pair_factor {x R b c : ℝ}
    (hx : 0 < x) (hR : 0 < R) (hb : 0 < b) (hc : 0 < c) (s : ℂ) :
    ((x * Real.sqrt (b * c) : ℝ) : ℂ) ^ s / (Real.sqrt (b * c) : ℂ) =
      (((x * R : ℝ) : ℂ) ^ s / (R : ℂ)) *
        ((b / R : ℝ) : ℂ) ^ ((s - 1) / 2) *
        ((c / R : ℝ) : ℂ) ^ ((s - 1) / 2) := by
  rw [quadraticPoisson_sqrt_pair_normalize hR hb hc]
  have hxR := mul_pos hx hR
  have hbR := div_pos hb hR
  have hcR := div_pos hc hR
  have he : x * (R * (Real.sqrt (b / R) * Real.sqrt (c / R))) =
      (x * R) * Real.sqrt (b / R) * Real.sqrt (c / R) := by ring
  rw [he]
  rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_pos hxR (Real.sqrt_pos.mpr hbR)).le
      (Real.sqrt_nonneg _),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hxR.le (Real.sqrt_nonneg _)]
  simp only [Complex.ofReal_mul]
  rw [← quadraticPoisson_sqrt_cpow_div hbR s, ← quadraticPoisson_sqrt_cpow_div hcR s]
  ring

def quadraticPoissonAnnularTwist (R q : ℝ) (z : ℂ) : ℂ :=
  ((q / R : ℝ) : ℂ) ^ z

theorem quadraticPoissonAnnularTwist_norm_le_one {R q : ℝ}
    (hR : 0 < R) (hqlo : R ≤ q) {z : ℂ} (hz : z.re ≤ 0) :
    ‖quadraticPoissonAnnularTwist R q z‖ ≤ 1 := by
  have hratio : 1 ≤ q / R := (le_div_iff₀ hR).mpr (by simpa using hqlo)
  rw [quadraticPoissonAnnularTwist,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hratio)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hratio hz

theorem quadraticPoissonAnnularTwist_norm_le_two {R q : ℝ}
    (hR : 0 < R) (hqlo : R ≤ q) (hqhi : q ≤ 2 * R) {z : ℂ} (hz : z.re ≤ 1) :
    ‖quadraticPoissonAnnularTwist R q z‖ ≤ 2 := by
  have hratio : 1 ≤ q / R := (le_div_iff₀ hR).mpr (by simpa using hqlo)
  have hratiohi : q / R ≤ 2 := (div_le_iff₀ hR).mpr hqhi
  rw [quadraticPoissonAnnularTwist,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hratio)]
  exact (Real.rpow_le_rpow_of_exponent_le hratio hz).trans
    (by simpa only [Real.rpow_one] using hratiohi)

theorem quadraticPoissonAnnularTwist_star {R q : ℝ} (hR : 0 < R) (hq : 0 < q)
    (z : ℂ) :
    star (quadraticPoissonAnnularTwist R q (star z)) =
      quadraticPoissonAnnularTwist R q z := by
  have ha : (((q / R : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (div_pos hq hR).le]
    exact Real.pi_ne_zero.symm
  change (starRingEnd ℂ) (((q / R : ℝ) : ℂ) ^ (starRingEnd ℂ) z) = _
  simpa only [Complex.conj_ofReal, quadraticPoissonAnnularTwist] using
    (Complex.conj_cpow ((q / R : ℝ) : ℂ) z ha).symm

theorem quadraticPoissonAnnularTwist_pair (R : ℝ) (q : ℝ) (hq : 0 < q)
    (hR : 0 < R) (coefficient : ℂ) (z : ℂ) :
    star (coefficient * quadraticPoissonAnnularTwist R q (star z)) =
      star coefficient * quadraticPoissonAnnularTwist R q z := by
  rw [star_mul, quadraticPoissonAnnularTwist_star hR hq]
  ring

def quadraticPoissonLine (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

theorem quadraticPoissonLine_re (σ t : ℝ) : (quadraticPoissonLine σ t).re = σ := by
  simp [quadraticPoissonLine]

theorem quadraticPoissonLine_cpow_integrable (H : ℝ → ℂ) (hHc : Continuous H)
    (hHi : Integrable H) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => H t * (x : ℂ) ^ quadraticPoissonLine σ t) := by
  have hcont : Continuous (fun t : ℝ => H t * (x : ℂ) ^ quadraticPoissonLine σ t) := by
    apply hHc.mul
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      quadraticPoissonLine]
    fun_prop
  refine (hHi.norm.mul_const (x ^ σ)).mono' hcont.aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, quadraticPoissonLine_re]

theorem quadraticPoissonLine_finite_sum {ι : Type*} (s : Finset ι)
    (H : ℝ → ℂ) (hHc : Continuous H) (hHi : Integrable H) (σ : ℝ)
    (x : ι → ℝ) (hx : ∀ i ∈ s, 0 < x i) (a : ι → ℂ) :
    (∑ i ∈ s, a i * ∫ t : ℝ, H t * (x i : ℂ) ^ quadraticPoissonLine σ t) =
      ∫ t : ℝ, H t * ∑ i ∈ s, a i * (x i : ℂ) ^ quadraticPoissonLine σ t := by
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum s (fun i hi =>
    (quadraticPoissonLine_cpow_integrable H hHc hHi σ (hx i hi)).const_mul (a i))]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The normalized Mellin coefficient preserves the actual annular coefficient
class and has a uniform squared-mass bound on every vertical line used here. -/
theorem quadraticPoissonAnnularTwist_coeffMass {κ : Type*} (cols : Finset κ)
    (u : κ → ℂ) (q : κ → ℝ) {R : ℝ} (hR : 0 < R)
    (hcols : ∀ b ∈ cols, R ≤ q b ∧ q b ≤ 2 * R) {z : ℂ} (hz : z.re ≤ 1) :
    QuadraticScale.coeffMass cols (fun b => u b * quadraticPoissonAnnularTwist R (q b) z) ≤
      4 * QuadraticScale.coeffMass cols u := by
  unfold QuadraticScale.coeffMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have htwist := quadraticPoissonAnnularTwist_norm_le_two hR
    (hcols b hb).1 (hcols b hb).2 hz
  rw [norm_mul, mul_pow]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htwist 2
  norm_num at hsq
  exact (mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖u b‖)).trans_eq (mul_comm _ _)

/-- Finite pairs may be separated before applying the divisor estimate, with
the column annulus retained literally in both normalized factors. -/
theorem quadraticPoissonLine_pair_sum {ι : Type*} (pairs : Finset ι)
    (H : ℝ → ℂ) (hHc : Continuous H) (hHi : Integrable H) (σ : ℝ)
    (a : ι → ℂ) (x b c : ι → ℝ) {R : ℝ} (hR : 0 < R)
    (hx : ∀ p ∈ pairs, 0 < x p) (hb : ∀ p ∈ pairs, 0 < b p)
    (hc : ∀ p ∈ pairs, 0 < c p) :
    (∑ p ∈ pairs, a p / (Real.sqrt (b p * c p) : ℂ) *
      ∫ t : ℝ, H t * ((x p * Real.sqrt (b p * c p) : ℝ) : ℂ) ^
        quadraticPoissonLine σ t) =
      ∫ t : ℝ, H t * ∑ p ∈ pairs,
        a p * (((x p * R : ℝ) : ℂ) ^ quadraticPoissonLine σ t / (R : ℂ)) *
          quadraticPoissonAnnularTwist R (b p) ((quadraticPoissonLine σ t - 1) / 2) *
          quadraticPoissonAnnularTwist R (c p) ((quadraticPoissonLine σ t - 1) / 2) := by
  rw [quadraticPoissonLine_finite_sum pairs H hHc hHi σ
    (fun p => x p * Real.sqrt (b p * c p))
    (fun p hp => mul_pos (hx p hp) (Real.sqrt_pos.mpr (mul_pos (hb p hp) (hc p hp))))]
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  calc
    _ = a p * (((x p * Real.sqrt (b p * c p) : ℝ) : ℂ) ^
        quadraticPoissonLine σ t / (Real.sqrt (b p * c p) : ℂ)) := by ring
    _ = _ := by
      rw [quadraticPoisson_normalized_pair_factor (hx p hp) hR (hb p hp) (hc p hp)]
      simp only [quadraticPoissonAnnularTwist]
      ring

end
end ArtinMatthews
