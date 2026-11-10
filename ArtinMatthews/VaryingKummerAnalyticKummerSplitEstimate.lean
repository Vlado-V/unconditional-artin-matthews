module

public import ArtinMatthews.Index
public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.KummerSplittingDiscriminant
public import ArtinMatthews.KummerSplittingPrimeIdeals
public import ArtinMatthews.VaryingKummerAnalyticSplitPrimeEstimate
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! The varying-q splitting count with the exact genuine zero-free input
still visible. All degree, discriminant and complete-splitting arithmetic
is proved for the actual Kummer field; no splitting-density axiom is used. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField OAI.PrimeDegreePackets Complex Set
open scoped Classical BigOperators
noncomputable section

lemma primeKummer_log_discr_add_degree_le {a : ℤ}
    (ha : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {q : ℕ} (hq : q.Prime) (haq : a.natAbs ≤ q) :
    Real.log |(discr (primeKummerField q a) : ℝ)|+
      (Module.finrank ℚ (primeKummerField q a) : ℝ) ≤
      14*(Module.finrank ℚ (primeKummerField q a) : ℝ)*Real.log (2*(q : ℝ)) := by
  have hdeg : (Module.finrank ℚ (primeKummerField q a) : ℝ) = (q : ℝ)*((q : ℝ)-1) := by
    rw [finrank_primeKummerField_of_large_prime ha ha1 ham1 hq haq]
    push_cast [Nat.cast_sub hq.one_lt.le]
    ring
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hlogq : (1/2 : ℝ) ≤ Real.log q := by
    have H := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hq2
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log (q : ℝ) ≤ Real.log (2*(q : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hn : 0 ≤ (Module.finrank ℚ (primeKummerField q a) : ℝ) := Nat.cast_nonneg _
  have hs : (q : ℝ)^2 ≤ 2*(Module.finrank ℚ (primeKummerField q a) : ℝ) := by rw [hdeg]; nlinarith
  have hd := primeKummerField_log_discr_le ha ha1 ham1 hq haq
  have hmul := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ Real.log q)
  have hlast := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 14*(Module.finrank ℚ (primeKummerField q a) : ℝ))
  nlinarith [mul_nonneg hn (show 0 ≤ 2*Real.log q-1 by linarith)]

/-- Uniform dyadic prime-index count with the genuine zero-location input.
Taking β=1−δ gives precisely the power-saving shape used by the paper,
once its separate fixed-width zero-free theorem is established. -/
theorem exists_primeKummer_split_count_bound_of_zero_region :
    ∃ C : ℝ,0 < C ∧ ∀ (a : ℤ),a ≠ 0 → a ≠ 1 → a ≠ -1 →
      ∀ (q : ℕ),q.Prime → a.natAbs ≤ q →
      ∀ (x β : ℝ) (S : Finset Nat.Primes),1 < x → 0 ≤ β →
      (∀ ρ : ℂ,mixedCompletedDedekindXi (primeKummerField q a) ρ = 0 → ρ.re ≤ β) →
      (∀ p ∈ S,x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*x ∧
        ¬ (p.val : ℤ) ∣ (q : ℤ) ∧ (a : ZMod p.val) ≠ 0 ∧ q ∣ multiplicativeIndex p a) →
      (S.card : ℝ) ≤ C*(x/((q : ℝ)*((q : ℝ)-1)*Real.log x)+
        x^β*Real.log (2*(q : ℝ))/Real.log x) := by
  obtain ⟨C,hC,hbound⟩ := exists_splitPrime_count_bound_of_zero_region.{0}
  refine ⟨14*C,by positivity,?_⟩
  intro a ha ha1 ham1 q hq haq x β S hx hβ hregion hS
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero a := ⟨ha⟩
  let n : ℝ := Module.finrank ℚ (primeKummerField q a)
  let d : ℝ := Real.log |(discr (primeKummerField q a) : ℝ)|+n
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := primeKummerField q a)
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hden : 0 < n*Real.log x := mul_pos hn hlogx
  have hN : n = (q : ℝ)*((q : ℝ)-1) := by
    dsimp [n]
    rw [finrank_primeKummerField_of_large_prime ha ha1 ham1 hq haq]
    push_cast [Nat.cast_sub hq.one_lt.le]
    ring
  have H := hbound (primeKummerField q a) x β S hx hβ hregion
    (fun p hp => ⟨(hS p hp).1,(hS p hp).2.1⟩)
    (fun p hp => primeKummer_normFiber_card_of_dvd_index p.property
      (hS p hp).2.2.1 (hS p hp).2.2.2.1 (hS p hp).2.2.2.2)
  have hd : d ≤ 14*n*Real.log (2*(q : ℝ)) := primeKummer_log_discr_add_degree_le ha ha1 ham1 hq haq
  have hp : 0 ≤ x^β := Real.rpow_nonneg hxpos.le _
  calc
    _ ≤ C*(x+x^β*d)/(n*Real.log x) := H
    _ ≤ C*(x+x^β*(14*n*Real.log (2*(q : ℝ))))/(n*Real.log x) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd hp)) hC.le
    _ ≤ 14*C*(x+x^β*n*Real.log (2*(q : ℝ)))/(n*Real.log x) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith [mul_nonneg hC.le hxpos.le]
    _ = _ := by
      rw [← hN]
      field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
