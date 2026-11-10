module

public import ArtinMatthews.VaryingKummerAnalyticZeroGrowth
public import ArtinMatthews.VaryingKummerAnalyticZeroReflection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Nonnegative zero-pole identity at an arbitrary complex basepoint to the
right of the critical strip. This generalizes the checked real-basepoint
argument without requiring conjugation symmetry. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth

open ArtinMatthews.ReusedGrowth
open Complex Set Metric Filter MeromorphicOn
open scoped Topology BigOperators

noncomputable def complexZeroPole (f : ℂ → ℂ) (s : ℂ) (ρ : ℂ) : ℝ :=
  (zeroMultiplicity f ρ : ℝ)*(1/(s-ρ)).re

lemma complexZeroPole_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {s : ℂ} (hs : 1 < s.re) (ρ : ℂ) :
    0 ≤ complexZeroPole f s ρ := by
  by_cases hm : zeroMultiplicity f ρ = 0
  · simp [complexZeroPole, hm]
  have hρ := hstrip ρ ((zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm)
  unfold complexZeroPole
  apply mul_nonneg (by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  simp only [one_div, Complex.inv_re, Complex.sub_re]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

lemma complexZeroPole_pair {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (s : ℂ) (ρ : ℂ) :
    complexZeroPole f s ρ + complexZeroPole f s (1-ρ) =
      ((zeroMultiplicity f ρ : ℂ)*(1/(s-ρ)-1/((1-s)-ρ))).re := by
  have HE : s-(1-ρ) = -((1-s)-ρ) := by ring
  simp only [complexZeroPole, zeroMultiplicity_reflection hfe, HE, one_div, inv_neg,
    Complex.neg_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    zero_mul, sub_zero, Complex.sub_re]
  ring

lemma diskPoleSum_sub_re_complex {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (s : ℂ) (R : ℝ) :
    (diskPoleSum f R s-diskPoleSum f R (1-s)).re =
      ∑ ρ ∈ zeroDiskFinset f R, (complexZeroPole f s ρ+complexZeroPole f s (1-ρ)) := by
  classical
  simp only [diskPoleSum, ← Finset.sum_sub_distrib, ← mul_sub,
    complexZeroPole_pair hfe]
  exact map_sum Complex.reAddGroupHom _ _

 

theorem hasSum_complexZeroPole {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (complexZeroPole f s) (logDeriv f s).re := by
  classical
  have hs0 : f s ≠ 0 := by
    intro h
    have HH := hstrip s h
    linarith
  have hs1 : f (1-s) ≠ 0 := by rwa [hfe]
  obtain ⟨r,hr,_,hS⟩ := exists_good_radii hf h0
  have HT := (Complex.continuous_re.tendsto _).comp (tendsto_diskPoleSum_sub hf h0 hg hr
    (Filter.Eventually.of_forall hS) hs0 hs1)
  have HT' : Tendsto (fun j => ∑ ρ ∈ zeroDiskFinset f (r j),
      (complexZeroPole f s ρ+complexZeroPole f s (1-ρ))) atTop (𝓝 (2*(logDeriv f s).re)) := by
    simpa only [Function.comp_def, diskPoleSum_sub_re_complex hfe,
      logDeriv_reflection hf hfe, Complex.sub_re, Complex.neg_re, sub_neg_eq_add, two_mul, Complex.add_re] using HT
  have HNN := complexZeroPole_nonneg hf h0 hstrip hs
  have Hsum : HasSum (fun ρ => complexZeroPole f s ρ+complexZeroPole f s (1-ρ))
      (2*(logDeriv f s).re) := by
    apply hasSum_of_nonneg_finite_exhaustion (fun ρ => add_nonneg (HNN ρ) (HNN (1-ρ)))
      (fun j => zeroDiskFinset f (r j)) _ HT'
    intro ρ hρ
    have Hm : zeroMultiplicity f ρ ≠ 0 := by
      intro H
      apply hρ
      simp [complexZeroPole, zeroMultiplicity_reflection hfe, H]
    filter_upwards [hr.eventually_ge_atTop ‖ρ‖] with j hj
    rw [mem_zeroDiskFinset, divisor_closedBall_eq_multiplicity hf hj]
    exact Hm
  have HS : Summable (complexZeroPole f s) := Hsum.summable.of_nonneg_of_le HNN
    (fun ρ => le_add_of_nonneg_right (HNN (1-ρ)))
  let e : ℂ ≃ ℂ := ⟨fun ρ => 1-ρ, fun ρ => 1-ρ, by intro ρ; ring, by intro ρ; ring⟩
  have HS' : Summable (fun ρ => complexZeroPole f s (1-ρ)) := e.summable_iff.mpr HS
  have HE : (∑' ρ, complexZeroPole f s (1-ρ)) = ∑' ρ, complexZeroPole f s ρ :=
    e.tsum_eq (complexZeroPole f s)
  have HH := Hsum.tsum_eq
  rw [HS.tsum_add HS', HE] at HH
  have HA : (∑' ρ, complexZeroPole f s ρ) = (logDeriv f s).re := by linarith
  exact HA ▸ HS.hasSum


end OAI.PrimeDegreePackets.AnalyticGrowth
