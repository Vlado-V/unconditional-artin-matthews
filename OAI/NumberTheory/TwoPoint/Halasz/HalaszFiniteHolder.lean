module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
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


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! The two finite Hölder steps used in the double mean-value argument. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_finite_weighted_power {ι : Type*} (S : Finset ι)
    (w f : ι → ℝ) (hw : ∀ i, 0≤w i) (hf : ∀ i, 0≤f i)
    {s : ℕ} (hs : 1≤s) :
    (∑ i∈S, w i*f i)^s ≤ (∑ i∈S,w i)^(s-1)*(∑ i∈S,w i*(f i)^s) := by
  have hsR : (1:ℝ)≤s := by exact_mod_cast hs
  have hs0 : (s:ℝ)≠0 := by exact_mod_cast (by omega : s≠0)
  have h := Real.inner_le_weight_mul_Lp_of_nonneg S hsR w f hw hf
  have hp := pow_le_pow_left₀ (sum_nonneg (fun i _ => mul_nonneg (hw i) (hf i))) h s
  have hW : 0≤∑ i∈S,w i := sum_nonneg (fun i _ => hw i)
  have hF : 0≤∑ i∈S,w i*(f i)^(s:ℝ) := sum_nonneg (fun i _ =>
    mul_nonneg (hw i) (Real.rpow_nonneg (hf i) _))
  have he : (1-(s:ℝ)⁻¹)*(s:ℝ)=((s-1:ℕ):ℝ) := by
    rw [Nat.cast_sub hs,Nat.cast_one]
    field_simp
  rw [mul_pow,← Real.rpow_mul_natCast hW,← Real.rpow_mul_natCast hF,
    he,inv_mul_cancel₀ hs0,Real.rpow_one,Real.rpow_natCast] at hp
  simpa only [Real.rpow_natCast] using hp

theorem halasz_finite_weighted_holder {ι : Type*} (S : Finset ι)
    (w f : ι → ℝ) (hw : ∀ i, 0≤w i) (hf : ∀ i, 0≤f i)
    {s : ℕ} (hs : 1≤s) :
    (∑ i∈S,w i*f i)^(2*s) ≤
      (∑ i∈S,w i)^(2*s-2)*(∑ i∈S,(w i)^2)*(∑ i∈S,(f i)^(2*s)) := by
  have h := halasz_finite_weighted_power S w f hw hf hs
  have hp := pow_le_pow_left₀ (pow_nonneg
    (sum_nonneg (fun i _ => mul_nonneg (hw i) (hf i))) s) h 2
  have hc := sum_mul_sq_le_sq_mul_sq S w (fun i => (f i)^s)
  rw [mul_pow,← pow_mul,← pow_mul] at hp
  rw [show s*2=2*s by omega,show (s-1)*2=2*s-2 by omega] at hp
  simp only [← pow_mul,show s*2=2*s by omega] at hc
  exact hp.trans (by
    have hh := mul_le_mul_of_nonneg_left hc (pow_nonneg
      (sum_nonneg (s := S) (fun i _ => hw i)) (2*s-2))
    simpa only [mul_assoc] using hh)

lemma halasz_complex_sum_power {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    {r : ℕ} (hr : 1≤r) :
    ‖∑ i∈S,z i‖^r≤(S.card:ℝ)^(r-1)*(∑ i∈S,‖z i‖^r) := by
  have hh := halasz_finite_weighted_power S (fun _ => (1:ℝ)) (fun i => ‖z i‖)
    (fun _ => zero_le_one) (fun _ => norm_nonneg _) hr
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S z) r
  exact hn.trans (by simpa using hh)

end TwoPointCorrelations

end OAI
