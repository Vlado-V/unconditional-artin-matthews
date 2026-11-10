module

public import ArtinMatthews.ArtinAbelianPrimeTower
public import ArtinMatthews.VaryingKummerAnalyticDedekindEulerLog
public import ArtinMatthews.VaryingKummerAnalyticDedekindEulerPrimeNorm
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishingLocal
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

/-! Absolute convergence of genuine abelian Artin Euler products, including
all inertia factors. The majorant is linear in the base-field degree. -/
noncomputable section
namespace ArtinMatthews.AbelianLocal
open OAI.PrimeDegreePackets ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField IsMulCommutative Classical BigOperators

private theorem character_norm_one {G : Type*} [Group G] [Finite G]
    (χ : G →* ℂˣ) (g : G) : ‖(χ g : ℂ)‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := G)).ne').mp
  have h : χ g ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have hn := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) h
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] using hn

private theorem norm_nat_cpow_neg_le {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) :
    ‖(N : ℂ) ^ (-s)‖ ≤ (N : ℝ) ^ (-σ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos, Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N))
    (neg_le_neg hs)

private theorem norm_nat_cpow_neg_le_half {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} (hs : 1 ≤ s.re) : ‖(N : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  apply (norm_nat_cpow_neg_le hN hs).trans
  rw [Real.rpow_neg_one]
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  simpa only [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNreal

private theorem twisted_log_norm_le {z : ℂ} (hz : ‖z‖ = 1)
    {N : ℕ} (hN : 2 ≤ N) {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖-Complex.log (1 - z * (N : ℂ) ^ (-s))‖ ≤ 2 * (N : ℝ) ^ (-σ) := by
  have hhalf : ‖z * (N : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    simpa only [norm_mul, hz, one_mul] using norm_nat_cpow_neg_le_half hN (hσ.trans hs)
  have hlog := Complex.norm_log_one_add_half_le_self
    (z := -(z * (N : ℂ) ^ (-s))) (by simpa using hhalf)
  simp only [norm_neg, ← sub_eq_add_neg, norm_mul, hz, one_mul] at hlog
  rw [norm_neg]
  calc
    _ ≤ (3 / 2) * ‖(N : ℂ) ^ (-s)‖ := hlog
    _ ≤ (3 / 2) * (N : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_left (norm_nat_cpow_neg_le hN hs) (by norm_num)
    _ ≤ 2 * (N : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]

/-- The principal logarithm of the actual one-dimensional inertia factor. -/
def abelianArtinPrimeLog (χ : Gal(E/F) →* ℂˣ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  if (abelianPrimeAbove F E P).val.inertia Gal(E/F) ≤ χ.ker then
    -Complex.log (1 - (χ (abelianPrimeFrobenius F E P) : ℂ) *
      (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))
  else 0

/-- The sum of prime-ideal logarithms above one rational prime. -/
def abelianArtinRationalLog (χ : Gal(E/F) →* ℂˣ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∑ P : idealsOverPrime F p, abelianArtinPrimeLog F E χ (primeOverHeightOne F p P) s

def abelianArtinEulerLog (χ : Gal(E/F) →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, abelianArtinRationalLog F E χ p s

/-- The genuine Artin Euler product, with every finite prime included. -/
def abelianArtinEulerProduct (χ : Gal(E/F) →* ℂˣ) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, abelianArtinRationalFactor F E χ p s

theorem abelianArtinRationalLog_norm_le (χ : Gal(E/F) →* ℂˣ) (p : Nat.Primes)
    {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖abelianArtinRationalLog F E χ p s‖ ≤ dedekindEulerLogMajorant F σ p := by
  calc
    _ ≤ ∑ P : idealsOverPrime F p,
        ‖abelianArtinPrimeLog F E χ (primeOverHeightOne F p P) s‖ := norm_sum_le _ _
    _ ≤ ∑ P : idealsOverPrime F p, 2 * (Ideal.absNorm P.val : ℝ) ^ (-σ) := by
      apply Finset.sum_le_sum
      intro P _
      unfold abelianArtinPrimeLog
      split_ifs
      · exact twisted_log_norm_le (character_norm_one χ _)
          (idealsOverPrime_norm_two_le F P.property) hσ hs
      · simp only [norm_zero]
        positivity
    _ = 2 * ∑ P : idealsOverPrime F p, (Ideal.absNorm P.val : ℝ) ^ (-σ) :=
      (Finset.mul_sum ..).symm
    _ ≤ 2 * ((Module.finrank ℚ F : ℝ) * (p : ℝ) ^ (-σ)) :=
      mul_le_mul_of_nonneg_left (prime_ideal_norm_series_le F p (by linarith)) (by norm_num)
    _ = _ := by unfold dedekindEulerLogMajorant; ring

theorem abelianArtinRationalLog_summable (χ : Gal(E/F) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => abelianArtinRationalLog F E χ p s) := by
  have h := (dedekindEulerLogMajorant_summable F hs).of_nonneg_of_le
    (fun p => norm_nonneg (abelianArtinRationalLog F E χ p s))
    (fun p => abelianArtinRationalLog_norm_le F E χ p hs.le le_rfl)
  exact h.of_norm

theorem abelianArtinRationalLog_exp (χ : Gal(E/F) →* ℂˣ) (p : Nat.Primes)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (abelianArtinRationalLog F E χ p s) =
      abelianArtinRationalFactor F E χ p s := by
  unfold abelianArtinRationalLog abelianArtinRationalFactor
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro P _
  unfold abelianArtinPrimeLog abelianArtinLocalFactor
  split_ifs
  · have hn : ‖(χ (abelianPrimeFrobenius F E (primeOverHeightOne F p P)) : ℂ) *
        (Ideal.absNorm P.val : ℂ) ^ (-s)‖ < 1 := by
      have hb : ‖(Ideal.absNorm P.val : ℂ) ^ (-s)‖ < 1 :=
        zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le F P.property)
      simpa only [norm_mul, character_norm_one, one_mul] using hb
    have hne : 1 - (χ (abelianPrimeFrobenius F E (primeOverHeightOne F p P)) : ℂ) *
        (Ideal.absNorm P.val : ℂ) ^ (-s) ≠ 0 := by
      intro h
      rw [← sub_eq_zero.mp h, norm_one] at hn
      exact (lt_irrefl _ hn)
    exact (Complex.exp_neg _).trans (congrArg Inv.inv (Complex.exp_log hne))
  · exact Complex.exp_zero

theorem abelianArtinEulerProduct_hasProd (χ : Gal(E/F) →* ℂˣ)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => abelianArtinRationalFactor F E χ p s)
      (abelianArtinEulerProduct F E χ s) := by
  have h := (abelianArtinRationalLog_summable F E χ hs).hasSum.cexp
  have he : HasProd (fun p : Nat.Primes => abelianArtinRationalFactor F E χ p s)
      (Complex.exp (abelianArtinEulerLog F E χ s)) :=
    h.congr_fun (fun p => (abelianArtinRationalLog_exp F E χ p hs).symm)
  exact he.multipliable.hasProd

theorem exp_abelianArtinEulerLog (χ : Gal(E/F) →* ℂˣ)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (abelianArtinEulerLog F E χ s) = abelianArtinEulerProduct F E χ s := by
  exact ((abelianArtinRationalLog_summable F E χ hs).hasSum.cexp.congr_fun
    (fun p => (abelianArtinRationalLog_exp F E χ p hs).symm)).tprod_eq.symm

theorem abelianArtinEulerProduct_ne_zero (χ : Gal(E/F) →* ℂˣ)
    {s : ℂ} (hs : 1 < s.re) : abelianArtinEulerProduct F E χ s ≠ 0 := by
  rw [← exp_abelianArtinEulerLog F E χ hs]
  exact Complex.exp_ne_zero _

end ArtinMatthews.AbelianLocal
