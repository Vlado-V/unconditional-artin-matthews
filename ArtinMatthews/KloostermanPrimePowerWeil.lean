module

public import ArtinMatthews.KloostermanSqrtEnvelope
public import ArtinMatthews.KloostermanPrimitiveWeil
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.Jacobsthal.Harmonic.CommonFrequencyLift


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine common-frequency lifting supplies the square-root gcd factor at every prime power. -/
noncomputable section
open OAI.Erdos970.ErdosKloosterman OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews.PrimePowerWeil

theorem sqrtEnvelope_prime_zero (p : ℕ) [Fact p.Prime] (h k : ℤ)
    (hh : (h:ZMod p)=0) (hk : (k:ZMod p)=0) : sqrtEnvelope p h k=8*(p:ℝ) := by
  have hd : p ∣ Int.gcd h k := Int.dvd_gcd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hh)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp hk)
  have hg := Nat.gcd_eq_left_iff_dvd.mpr hd
  have he := sqrtEnvelope_prime_power p 1 h k
  norm_num at he
  rw [he,hg,mul_assoc,Real.mul_self_sqrt (Nat.cast_nonneg p)]

theorem standardSum_prime_sqrtEnvelope (p : ℕ) [Fact p.Prime] (h k : ℤ) :
    ‖standardSum p h k‖ ≤ sqrtEnvelope p h k := by
  have primitive (hnot : (h:ZMod p) ≠ 0 ∨ (k:ZMod p) ≠ 0) :
      ‖standardSum p h k‖ ≤ sqrtEnvelope p h k := by
    simpa only [pow_one] using
      (standardSum_primitive_prime_power p 1 (by decide) h k hnot).trans
        (sqrtEnvelope_ge_primitive p 1 (by decide) h k)
  by_cases hh : (h:ZMod p)=0
  · by_cases hk : (k:ZMod p)=0
    · have he : standardSum p h k=(Fintype.card (ZMod p)ˣ:ℂ) := by
        simp only [standardSum,hh,hk,sum_zero_zero,← Nat.card_eq_fintype_card]
      have hc : (Fintype.card (ZMod p)ˣ:ℝ) ≤ p := by
        have hc := Fintype.card_le_of_injective (fun u : (ZMod p)ˣ => (u:ZMod p)) Units.val_injective
        simpa only [ZMod.card] using (show (Fintype.card (ZMod p)ˣ:ℝ) ≤ Fintype.card (ZMod p) by exact_mod_cast hc)
      rw [he,sqrtEnvelope_prime_zero p h k hh hk]
      calc
        _ = (Fintype.card (ZMod p)ˣ:ℝ) := by simp
        _ ≤ (p:ℝ) := hc
        _ ≤ 8*(p:ℝ) := by nlinarith [show (0:ℝ) ≤ p from Nat.cast_nonneg p]
    · exact primitive (Or.inr hk)
  · exact primitive (Or.inl hh)

theorem standardSum_prime_power_sqrtEnvelope (p : ℕ) [Fact p.Prime] :
    ∀ a : ℕ, 0 < a → ∀ h k : ℤ, ‖standardSum (p^a) h k‖ ≤ sqrtEnvelope (p^a) h k := by
  intro a
  induction a with
  | zero => intro ha; omega
  | succ a ih =>
    intro ha h k
    by_cases haz : a=0
    · subst a
      simpa only [Nat.zero_add,pow_one] using standardSum_prime_sqrtEnvelope p h k
    have ha0 : 0 < a := by omega
    by_cases hprimitive : (h:ZMod p) ≠ 0 ∨ (k:ZMod p) ≠ 0
    · exact (standardSum_primitive_prime_power p (a+1) (by omega) h k hprimitive).trans
        (sqrtEnvelope_ge_primitive p (a+1) (by omega) h k)
    push Not at hprimitive
    obtain ⟨hh,hk⟩ := hprimitive
    obtain ⟨h',rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hh
    obtain ⟨k',rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp hk
    rw [common_frequency_lift p a ha0,norm_mul]
    have hp : ‖(p:ℂ)‖=(p:ℝ) := by simp
    rw [hp]
    exact (mul_le_mul_of_nonneg_left (ih ha0 h' k') (Nat.cast_nonneg p)).trans
      (sqrtEnvelope_common_frequency_scale p a h' k')

end ArtinMatthews.PrimePowerWeil
