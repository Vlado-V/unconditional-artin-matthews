module

public import ArtinMatthews.HeckeIntervalSharpComparison
public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.HeckeCubicIntervalSmooth
public import ArtinMatthews.HeckePrimeLogSaving
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

/-! The actual sharp long-prime interval estimate of Lemma 4.1. Both the
moving cutoff and its boundary error are discharged uniformly. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths Filter

theorem cubicNumeratorPrimeSharp_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (A₀ B δ D : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (χ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ m n : ℕ, m ≤ n → H ≤ m → (n : ℝ) ≤ 2*H →
      ∀ t : ℝ, |t| ≤ x^B →
      ‖heckeSharpPrimeSum (cubicNumeratorHeckeCharacter A hA) χ m n t‖ ≤
        34*H*(Real.log x)^(-D) := by
  have hE : 0 < D+2 := by linarith
  have hwidth := (tendsto_rpow_neg_atTop hE).comp Real.tendsto_log_atTop
  filter_upwards [cubicNumeratorIntervalSmooth_all_log A hA hnoncube A₀ B δ D (D+2) hB hδ hE,
    heckePrime_uniform_power_log_saving 8 0 δ D (by norm_num) (by norm_num) hδ,
    hwidth.eventually (eventually_lt_nhds (show (0 : ℝ) < 1/2 by norm_num)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x hsmooth hconst hwidth hlog1 hx
  intro q _ hq χ H hH m n hmn hmH hnH t ht
  have hHp : 0 < H := (Real.rpow_pos_of_pos (by linarith : 0 < x) δ).trans_le hH
  have hm0 : 0 < (m : ℝ) := hHp.trans_le hmH
  have hn0 : 0 < (n : ℝ) := hm0.trans_le (by exact_mod_cast hmn)
  have hu : 0 ≤ Real.log ((m : ℝ)/H) := Real.log_nonneg ((one_le_div hHp).mpr hmH)
  have huv : Real.log ((m : ℝ)/H) ≤ Real.log ((n : ℝ)/H) :=
    Real.log_le_log (div_pos hm0 hHp) ((div_le_div_iff_of_pos_right hHp).mpr (by exact_mod_cast hmn))
  have hv : Real.log ((n : ℝ)/H) ≤ Real.log 2 :=
    Real.log_le_log (div_pos hn0 hHp) ((div_le_iff₀ hHp).mpr hnH)
  have heps : 0 < (Real.log x)^(-(D+2)) := Real.rpow_pos_of_pos (Real.log_pos hx) _
  have hs := hsmooth q hq χ H hH t ht _ _ hu huv hv
  have hc := heckeInterval_sharp_comparison (cubicNumeratorHeckeCharacter A hA) χ
    heps hwidth.le hHp m n hmn hmH hnH t
  have hepsbound : (Real.log x)^(-(D+2)) ≤ (Real.log x)^(-D) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
  have h8 : 8 ≤ H*(Real.log x)^(-D) := by simpa only [Real.rpow_zero, mul_one] using hconst H hH
  have herror : 32*(Real.log x)^(-(D+2))*H+8 ≤ 33*H*(Real.log x)^(-D) := by
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hepsbound (by norm_num : (0 : ℝ) ≤ 32)) hHp.le
    nlinarith
  rw [norm_sub_rev] at hc
  exact ((norm_le_insert' _ _).trans (add_le_add hs (hc.trans herror))).trans_eq (by ring)

end ArtinMatthews
