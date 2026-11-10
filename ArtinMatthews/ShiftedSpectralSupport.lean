module

public import ArtinMatthews.ShiftedConvolutionCoefficients
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Int.Lemmas
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite dual coefficient sequence has the claimed frequency
range, before applying any spectral estimate. -/

noncomputable section
namespace ArtinMatthews

theorem shiftedSpectralFrequency_bound (m3 m4 K1 K2 k1 k2 : ℕ)
    (h1 : k1≤K1) (h2 : k2≤K2) :
    ((m4 : ℤ)*k2-(m3 : ℤ)*k1).natAbs ≤ m3*K1+m4*K2 := by
  have hb1 : m4*k2≤m3*K1+m4*K2 :=
    (Nat.mul_le_mul_left m4 h2).trans (Nat.le_add_left _ _)
  have hb2 : m3*k1≤m3*K1+m4*K2 :=
    (Nat.mul_le_mul_left m3 h1).trans (Nat.le_add_right _ _)
  simpa only [Nat.cast_mul] using Int.natAbs_coe_sub_coe_le_of_le hb1 hb2

theorem shiftedConvolutionCoeff_eq_zero_outside (S T : Finset ℕ)
    (m3 m4 D K1 K2 : ℕ) (a b : ℕ → ℂ)
    (hS : ∀ k∈S, k≤K1) (hT : ∀ k∈T, k≤K2)
    (r : ℤ) (hr : m3*K1+m4*K2<r.natAbs) :
    shiftedConvolutionCoeff S T m3 m4 D a b r=0 := by
  unfold shiftedConvolutionCoeff
  apply Finset.sum_eq_zero
  intro k1 hk1
  apply Finset.sum_eq_zero
  intro k2 hk2
  have hne : (m4 : ℤ)*k2-(m3 : ℤ)*k1≠r := by
    intro h
    have hb := shiftedSpectralFrequency_bound m3 m4 K1 K2 k1 k2 (hS k1 hk1) (hT k2 hk2)
    rw [h] at hb
    omega
  simp only [hne,false_and,ite_false]

end ArtinMatthews
