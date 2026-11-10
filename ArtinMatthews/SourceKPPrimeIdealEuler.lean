module

public import ArtinMatthews.ProbeEulerPrimeNorms
public import ArtinMatthews.VaryingKummerAnalyticDedekindEulerLog
public import ArtinMatthews.ArtinAbelianPrimeTower
public import ArtinMatthews.ProbeIdealSourceRegions
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
public import Mathlib.RingTheory.Ideal.Int
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exterior scattering factor is an actual product over the finite
places. This file refines the checked rational-prime packets to individual
prime ideals and removes an arbitrary finite set of places exactly. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic AbelianLocal OAI.PrimeDegreePackets
open scoped NumberField BigOperators
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

private def sourceKPPrimePacketMap (a : Σ p : Nat.Primes, idealsOverPrime K p) : ProbePrime K :=
  primeOverHeightOne K a.1 a.2

private theorem sourceKPPrimePacketMap_injective : Function.Injective (sourceKPPrimePacketMap K) := by
  rintro ⟨p, P⟩ ⟨q, Q⟩ h
  have hPQ : P.val = Q.val := congrArg HeightOneSpectrum.asIdeal h
  obtain ⟨e, he⟩ := idealsOverPrime_norm_power K p.property P.property
  obtain ⟨f, hf⟩ := idealsOverPrime_norm_power K q.property Q.property
  have he0 : e ≠ 0 := by
    intro h
    rw [h, pow_zero] at he
    have hn := idealsOverPrime_norm_two_le K P.property
    omega
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, pow_zero] at hf
    have hn := idealsOverPrime_norm_two_le K Q.property
    omega
  have hpq : (p : ℕ) = (q : ℕ) :=
    (p.property.pow_inj' q.property he0 hf0 (he.symm.trans (hPQ ▸ hf))).1
  have hpq' : p = q := Subtype.ext hpq
  subst q
  exact congrArg (Sigma.mk p) (Subtype.ext hPQ)

private theorem sourceKPPrimePacketMap_surjective : Function.Surjective (sourceKPPrimePacketMap K) := by
  intro P
  let : P.asIdeal.IsPrime := P.isPrime
  let : NeZero P.asIdeal := ⟨P.ne_bot⟩
  let p : Nat.Primes := ⟨Ideal.absNorm (P.asIdeal.under ℤ), Nat.absNorm_under_prime P.asIdeal⟩
  have hp : (p : 𝓞 K) ∈ P.asIdeal := by
    have hmem : ((p : ℕ) : ℤ) ∈ P.asIdeal.under ℤ := by
      rw [← Int.ideal_span_absNorm_eq_self (P.asIdeal.under ℤ)]
      exact Ideal.subset_span (Set.mem_singleton _)
    simpa only [Ideal.mem_under, map_natCast] using hmem
  let Q : idealsOverPrime K p := ⟨P.asIdeal,
    (mem_idealsOverPrime_iff K p.property.ne_zero P.asIdeal).mpr ⟨P.isPrime, hp⟩⟩
  exact ⟨⟨p, Q⟩, HeightOneSpectrum.ext rfl⟩

def sourceKPPrimePacketEquiv : (Σ p : Nat.Primes, idealsOverPrime K p) ≃ ProbePrime K :=
  Equiv.ofBijective (sourceKPPrimePacketMap K)
    ⟨sourceKPPrimePacketMap_injective K, sourceKPPrimePacketMap_surjective K⟩

theorem sourceKPPrimeIdealPower_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun P : ProbePrime K => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ)) := by
  have h := (HeckeIdealMobius.normSeries_summable K (show 0 < σ-1 by linarith)).comp_injective
    (i := fun P : ProbePrime K => (⟨P.asIdeal, P.ne_bot⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥}))
    (by intro P Q h; exact HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val h))
  convert h using 1
  ext P
  congr 1
  ring

def sourceKPPrimeIdealLog (P : ProbePrime K) (s : ℂ) : ℂ :=
  -Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))

theorem sourceKPPrimeIdealLog_norm_le (P : ProbePrime K) {s : ℂ} (hs : 1 < s.re) :
    ‖sourceKPPrimeIdealLog K P s‖ ≤ 2 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
  have hQ : 1 < (Ideal.absNorm P.asIdeal : ℝ) := probeIdealPrime_norm_gt_one K P
  have hn : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ =
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
  have hhalf : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ ≤ 1/2 := by
    rw [hn]
    calc
      _ ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)
      _ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1/2 := by
        rw [inv_eq_one_div]
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        exact_mod_cast (show 2 ≤ Ideal.absNorm P.asIdeal by exact_mod_cast hQ)
  have hl := Complex.norm_log_one_add_half_le_self
    (z := -(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) (by simpa using hhalf)
  rw [norm_neg, ← sub_eq_add_neg] at hl
  change ‖-Complex.log (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))‖ ≤ _
  rw [norm_neg]
  have hnonneg := norm_nonneg ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s))
  calc
    _ ≤ (3/2) * ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ := hl
    _ ≤ 2 * ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ := by nlinarith
    _ = _ := by rw [hn]

theorem sourceKPPrimeIdealLog_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun P : ProbePrime K => sourceKPPrimeIdealLog K P s) := by
  apply Summable.of_norm
  exact ((sourceKPPrimeIdealPower_summable K hs).mul_left 2).of_nonneg_of_le
    (fun P => norm_nonneg _) (fun P => sourceKPPrimeIdealLog_norm_le K P hs)

theorem sourceKPPrimeIdealLog_sum {s : ℂ} (hs : 1 < s.re) :
    (∑' P : ProbePrime K, sourceKPPrimeIdealLog K P s) = dedekindEulerLog K s := by
  rw [← (sourceKPPrimePacketEquiv K).tsum_eq]
  have h := (sourceKPPrimePacketEquiv K).summable_iff.mpr (sourceKPPrimeIdealLog_summable K hs)
  change Summable (fun t : Σ p : Nat.Primes, idealsOverPrime K p =>
    sourceKPPrimeIdealLog K (sourceKPPrimePacketEquiv K t) s) at h
  rw [h.tsum_sigma]
  congr 1
  ext p
  rw [tsum_fintype]
  rfl

theorem sourceKPPrimeIdealEuler_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : ProbePrime K => (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹)
      (dedekindZeta K s) := by
  have h := (sourceKPPrimeIdealLog_summable K hs).hasSum.cexp
  rw [sourceKPPrimeIdealLog_sum K hs, exp_dedekindEulerLog_eq_dedekindZeta K hs] at h
  apply h.congr_fun
  intro P
  change (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹ = Complex.exp (sourceKPPrimeIdealLog K P s)
  rw [sourceKPPrimeIdealLog, Complex.exp_neg, Complex.exp_log]
  intro hz
  have hn : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one (probeIdealPrime_norm_gt_one K P)),
      Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (probeIdealPrime_norm_gt_one K P) (by linarith)
  rw [← sub_eq_zero.mp hz, norm_one] at hn
  exact (lt_irrefl _ hn)

end
end ArtinMatthews
