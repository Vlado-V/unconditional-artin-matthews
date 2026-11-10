module

public import ArtinMatthews.HeckePrimeSmoothSums
public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.HeckeIntervalCutoff
public import ArtinMatthews.HeckeDirichletTwistNonprincipal
public import ArtinMatthews.HeckeIntervalLogSaving
public import ArtinMatthews.HeckeIntervalPrimePower
public import ArtinMatthews.HeckePrimeLongParameters
public import ArtinMatthews.HeckePrimeScaleConversion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual moving interval smooth prime cancellation. The cutoff depends
on both endpoints and on x; all constants are uniform over those choices. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths Filter

theorem cubicNumeratorIntervalSmooth_power (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ K H₀ : ℝ, 0 < K ∧ 0 < H₀ ∧ ∃ k : ℕ, 2 ≤ k ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ Real.log 2 →
      ∀ H : ℝ, H₀ ≤ H → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ((heckeDirichletTwist (cubicNumeratorHeckeCharacter A hA) χ).modulus.absNorm : ℝ) ≤ H →
      ∀ t : ℝ, |t| ≤ H^B →
      ‖heckeRationalPrimeSmoothSum (cubicNumeratorHeckeCharacter A hA) χ
        (heckeLogIntervalCutoff ε u v) H t‖ ≤ (K/ε^k)*H^(29/32 : ℝ) := by
  obtain ⟨C, H₀, hC, _, k, hk, hpoly⟩ := heckeInterval_primePolynomial_power B hB
  let b := 2*Real.exp 1
  refine ⟨C+3*max 1 b, max H₀ 1, by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), k, hk, ?_⟩
  intro ε hε hε1 u v hu huv hv H hH q _ χ hmod t ht
  have hH1 : 1 ≤ H := (le_max_right _ _).trans hH
  have hp := hpoly ε hε hε1 u v hu huv hv H ((le_max_left _ _).trans hH)
    (heckeDirichletTwist _ χ) (cubicNumeratorHeckeDirichletTwist_nonprincipal A hA hnoncube χ)
    hmod t ht
  rw [heckeRationalPrimeSmoothSum_eq_finite _ χ _ 1 b H t (by linarith)
    (heckeLogIntervalCutoff_uniform_support hε hε1 hu huv hv)]
  have hb := heckeRationalPrimeSum_of_polynomial_power _ χ (heckeLogIntervalCutoff ε u v)
    b H t (C/ε^k) 1 hH1 (by norm_num) (heckeLogIntervalCutoff_norm_le_one hε huv) hp
  have hwidth : 3*max 1 b ≤ (3*max 1 b)/ε^k := by
    apply (le_div_iff₀ (pow_pos hε k)).mpr
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hε.le hε1)
  apply hb.trans
  simp only [mul_one]
  calc
    _ ≤ (C/ε^k+(3*max 1 b)/ε^k)*H^(29/32 : ℝ) := by gcongr
    _ = _ := by ring

theorem cubicNumeratorIntervalSmooth_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (A₀ B δ D E : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hE : 0 < E) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (χ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ t : ℝ, |t| ≤ x^B → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ Real.log 2 →
      ‖heckeRationalPrimeSmoothSum (cubicNumeratorHeckeCharacter A hA) χ
        (heckeLogIntervalCutoff ((Real.log x)^(-E)) u v) H t‖ ≤ H*(Real.log x)^(-D) := by
  obtain ⟨K, H₀, hK, _, k, _, hpower⟩ := cubicNumeratorIntervalSmooth_power A hA hnoncube
    (B/δ) (div_nonneg hB hδ.le)
  have hwidth := (tendsto_rpow_neg_atTop hE).comp Real.tendsto_log_atTop
  filter_upwards [heckeDirichletTwist_modulus_eventually (cubicNumeratorHeckeCharacter A hA) A₀ δ hδ,
    heckeInterval_uniform_power_log_saving K (29/32) δ D E k hK.le (by norm_num) hδ,
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop H₀),
    hwidth.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop (1 : ℝ)] with x hmod hsave hlarge hwidth hx
  intro q _ hq χ H hH t ht u v hu huv hv
  apply (hpower _ (Real.rpow_pos_of_pos (Real.log_pos hx) _) hwidth.le u v hu huv hv H
    (hlarge.trans hH) q χ ((hmod q hq χ).trans hH) t
    (ht.trans (heckePrime_frequency_transport (by linarith) hδ hB hH))).trans
  exact hsave H hH

end ArtinMatthews
