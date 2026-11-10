module

public import ArtinMatthews.VaryingKummerAnalyticDedekindPrimePowerTerms
public import ArtinMatthews.VaryingKummerAnalyticDedekindLogDerivativeBound
public import ArtinMatthews.VaryingKummerAnalyticDedekindEulerDerivative
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Dedekind logarithmic derivative as an absolutely convergent
series over the actual prime ideals and all of their positive powers. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section

open NumberField OAI.PrimeDegreePackets
open scoped NumberField BigOperators Classical

variable (K : Type*) [Field K] [NumberField K]

def dedekindEulerMangoldtLocal (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∑ P : idealsOverPrime K p, primePowerMangoldtLocal (Ideal.absNorm P.val) s

def DedekindPrimePowerIndex : Type _ :=
  Σ p : Nat.Primes, Σ _P : idealsOverPrime K p, ℕ

def dedekindPrimePowerTerm (i : DedekindPrimePowerIndex K) (s : ℂ) : ℂ :=
  primePowerMangoldtTerm (Ideal.absNorm i.2.1.val) i.2.2 s

theorem dedekindEulerLocalLog_hasDerivAt (p : Nat.Primes)
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (dedekindEulerLocalLog K p) (-dedekindEulerMangoldtLocal K p s) s := by
  have hd : HasDerivAt
      (fun z : ℂ => ∑ P : idealsOverPrime K p,
        -Complex.log (1-(Ideal.absNorm P.val : ℂ)^(-z)))
      (∑ P : idealsOverPrime K p, -primePowerMangoldtLocal (Ideal.absNorm P.val) s) s := by
    exact HasDerivAt.fun_sum fun P _ =>
      primePowerMangoldtLog_hasDerivAt (idealsOverPrime_norm_two_le K P.property) hs
  change HasDerivAt (fun z : ℂ => ∑ P : idealsOverPrime K p,
    -Complex.log (1-(Ideal.absNorm P.val : ℂ)^(-z)))
    (-(∑ P : idealsOverPrime K p, primePowerMangoldtLocal (Ideal.absNorm P.val) s)) s
  simpa only [Finset.sum_neg_distrib] using hd

theorem dedekindZeta_neg_logDeriv_hasSum_local {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Nat.Primes => dedekindEulerMangoldtLocal K p s)
      (-logDeriv (NumberField.dedekindZeta K) s) := by
  have h := dedekindZeta_logDeriv_hasSum_deriv K hs
  simp_rw [(dedekindEulerLocalLog_hasDerivAt K _ hs).deriv] at h
  simpa only [neg_neg] using h.neg

theorem dedekindPrimePowerLocal_summable_norm (p : Nat.Primes)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun i : (Σ _P : idealsOverPrime K p, ℕ) =>
      ‖primePowerMangoldtTerm (Ideal.absNorm i.1.val) i.2 s‖) := by
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun P => (primePowerMangoldtTerm_norm_hasSum
    (idealsOverPrime_norm_two_le K P.property) hs).summable, Summable.of_finite⟩

theorem dedekindPrimePowerLocal_norm_hasSum (p : Nat.Primes)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun i : (Σ _P : idealsOverPrime K p, ℕ) =>
      ‖primePowerMangoldtTerm (Ideal.absNorm i.1.val) i.2 s‖)
      (dedekindEulerMangoldtLocal K p (s.re : ℂ)).re := by
  have houter : HasSum (fun P : idealsOverPrime K p =>
      (primePowerMangoldtLocal (Ideal.absNorm P.val) (s.re : ℂ)).re)
      (dedekindEulerMangoldtLocal K p (s.re : ℂ)).re :=
    Complex.hasSum_re (hasSum_fintype _)
  exact houter.sigma_of_hasSum (fun P => primePowerMangoldtTerm_norm_hasSum
    (idealsOverPrime_norm_two_le K P.property) hs) (dedekindPrimePowerLocal_summable_norm K p hs)

theorem dedekindPrimePowerLocal_hasSum (p : Nat.Primes)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun i : (Σ _P : idealsOverPrime K p, ℕ) =>
      primePowerMangoldtTerm (Ideal.absNorm i.1.val) i.2 s)
      (dedekindEulerMangoldtLocal K p s) := by
  exact (hasSum_fintype _).sigma_of_hasSum (fun P => primePowerMangoldtTerm_hasSum
    (idealsOverPrime_norm_two_le K P.property) hs)
    (dedekindPrimePowerLocal_summable_norm K p hs).of_norm

theorem dedekindPrimePower_summable_norm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun i : DedekindPrimePowerIndex K => ‖dedekindPrimePowerTerm K i s‖) := by
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun p => dedekindPrimePowerLocal_summable_norm K p hs, ?_⟩
  have h := (Complex.hasSum_re (dedekindZeta_neg_logDeriv_hasSum_local K
    (s := (s.re : ℂ)) (by simpa using hs))).summable
  exact h.congr fun p => (dedekindPrimePowerLocal_norm_hasSum K p hs).tsum_eq.symm

/-- The literal prime-ideal power series, with no Mangoldt-series premise. -/
theorem dedekindZeta_neg_logDeriv_primePower_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun i : DedekindPrimePowerIndex K => dedekindPrimePowerTerm K i s)
      (-logDeriv (NumberField.dedekindZeta K) s) :=
  (dedekindZeta_neg_logDeriv_hasSum_local K hs).sigma_of_hasSum
    (fun p => dedekindPrimePowerLocal_hasSum K p hs) (dedekindPrimePower_summable_norm K hs).of_norm

/-- The complete absolute series has its exact positive real-axis sum. -/
theorem dedekindPrimePower_norm_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun i : DedekindPrimePowerIndex K => ‖dedekindPrimePowerTerm K i s‖)
      (-logDeriv (NumberField.dedekindZeta K) (s.re : ℂ)).re :=
  (Complex.hasSum_re (dedekindZeta_neg_logDeriv_hasSum_local K
    (s := (s.re : ℂ)) (by simpa using hs))).sigma_of_hasSum
    (fun p => dedekindPrimePowerLocal_norm_hasSum K p hs) (dedekindPrimePower_summable_norm K hs)

theorem dedekindPrimePower_norm_tsum_le {s : ℂ} (hs : (3/2 : ℝ) ≤ s.re) :
    (∑' i : DedekindPrimePowerIndex K, ‖dedekindPrimePowerTerm K i s‖) ≤
      dedekindLogDerivUniformConstant*(Module.finrank ℚ K : ℝ) := by
  rw [(dedekindPrimePower_norm_hasSum K (by linarith : 1 < s.re)).tsum_eq]
  exact (Complex.re_le_norm _).trans (by
    simpa only [norm_neg] using dedekindZeta_logDeriv_norm_le K (s := (s.re : ℂ))
      (by simpa using hs))

end
end ArtinMatthews.VaryingKummerAnalytic
