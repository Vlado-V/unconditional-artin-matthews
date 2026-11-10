module

public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! The exact residue restriction in the double-Voronoi complete sum,
under the stationary equation and the full common-prime factor split. -/

namespace ArtinMatthews

theorem doubleVoronoi_stationary_congruence
    (d R m₃ m₄ k₁ k₂ u A₀ : ℤ) (hR : R ≠ 0)
    (hfactor : m₃-m₄ = R*A₀) (hcop : IsCoprime d (m₃*A₀))
    (hstationary : Int.ModEq (d*R)
      ((m₃-m₄)*m₃*m₄*u^2) (m₄*k₂-m₃*k₁)) :
    Int.ModEq (d*R) (m₃^2*k₁) (m₄^2*k₂) ↔
      Int.ModEq d k₁ (m₄^2*u^2) := by
  have hdiff : Int.ModEq (d*R) (m₄^2*k₂-m₃^2*k₁)
      (m₃*(m₃-m₄)*(m₄^2*u^2-k₁)) := by
    apply Int.modEq_of_dvd
    convert dvd_mul_of_dvd_right hstationary.dvd (-m₄) using 1
    ring
  have hcancel (t : ℤ) : d*R ∣ R*t ↔ d ∣ t := by
    constructor
    · intro h
      apply Int.dvd_of_mul_dvd_mul_left hR
      simpa only [mul_comm d R] using h
    · intro h
      simpa only [mul_comm d R] using mul_dvd_mul_left R h
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  calc
    d*R ∣ m₄^2*k₂-m₃^2*k₁ ↔ d*R ∣ m₃*(m₃-m₄)*(m₄^2*u^2-k₁) := hdiff.dvd_iff
    _ ↔ d*R ∣ R*((m₃*A₀)*(m₄^2*u^2-k₁)) := by
      rw [hfactor]
      have heq : m₃*(R*A₀)*(m₄^2*u^2-k₁) = R*((m₃*A₀)*(m₄^2*u^2-k₁)) := by ring
      rw [heq]
    _ ↔ d ∣ (m₃*A₀)*(m₄^2*u^2-k₁) := hcancel _
    _ ↔ d ∣ m₄^2*u^2-k₁ := hcop.dvd_mul_left_iff

end ArtinMatthews
