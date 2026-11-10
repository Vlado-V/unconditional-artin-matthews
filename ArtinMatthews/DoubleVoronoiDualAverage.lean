module

public import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount
public import OAI.NumberTheory.Jacobsthal.Sieve.ResidueFibres
public import ArtinMatthews.DoubleVoronoiPhase
public import ArtinMatthews.DoubleVoronoiScaledAverage
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

/-! Exact finite character arithmetic after the two Voronoi transforms.
The normalized congruence average becomes a square-residue weight on the
ordinary complete Kloosterman sum. -/

namespace ArtinMatthews
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman.PrimePower
noncomputable section

/-- The lifted d-character parameter is square-zero at modulus H*d
whenever d divides H. -/
theorem circleCorrection_square_zero (H d : ℕ) (hdH : d ∣ H) (j : ZMod d) :
    ((H : ZMod (H*d))*(j.val : ZMod (H*d)))^2=0 := by
  have hdvd : H*d ∣ H^2 := by
    obtain ⟨r,rfl⟩ := hdH
    exact ⟨r, by ring⟩
  have hH : (H : ZMod (H*d))^2=0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact hdvd
  rw [mul_pow, hH, zero_mul]

/-- The exact post-transformation additive phase for a fixed circle
numerator and the lifted d-congruence parameter. -/
def doubleVoronoiDualPhase (H d : ℕ) (hdH : d ∣ H)
    (m₃ m₄ a : (ZMod (H*d))ˣ) (k₁ k₂ : ZMod (H*d)) (j : ZMod d) : ZMod (H*d) :=
  let h : ZMod (H*d) := (H : ZMod (H*d))*(j.val : ZMod (H*d))
  ((m₃ : ZMod (H*d))-(m₄ : ZMod (H*d)))*(a : ZMod (H*d)) -
    h*(m₄ : ZMod (H*d))*(a : ZMod (H*d)) -
    k₁*(↑(m₄*a*shiftUnit 1 h (circleCorrection_square_zero H d hdH j))⁻¹ : ZMod (H*d)) -
    k₂*(↑(-(m₃*a))⁻¹ : ZMod (H*d))

/-- No d-factor is lost: the normalized d-average is exactly the
Kloosterman phase times its residue restriction. -/
theorem doubleVoronoi_dual_average (H d : ℕ) [NeZero H] [NeZero d] (hdH : d ∣ H)
    (m₃ m₄ a : (ZMod (H*d))ˣ) (k₁ k₂ : ZMod (H*d)) :
    (∑ j : ZMod d, ZMod.stdAddChar (doubleVoronoiDualPhase H d hdH m₃ m₄ a k₁ k₂ j)) /
      (d : ℂ) =
    ZMod.stdAddChar (((m₃ : ZMod (H*d))-(m₄ : ZMod (H*d)))*(a : ZMod (H*d)) +
      (↑(m₃*m₄)⁻¹ : ZMod (H*d))*((m₄ : ZMod (H*d))*k₂-(m₃ : ZMod (H*d))*k₁)*
        (↑a⁻¹ : ZMod (H*d))) *
      (if reduction H d k₁ = (ZMod.unitsMap (dvd_mul_left d H) (m₄*a) : ZMod d)^2
        then 1 else 0) := by
  have hphase (j : ZMod d) := doubleVoronoi_phase_identity m₃ m₄ a k₁ k₂
    ((H : ZMod (H*d))*(j.val : ZMod (H*d))) (circleCorrection_square_zero H d hdH j)
  unfold doubleVoronoiDualPhase
  simp_rw [hphase]
  exact doubleVoronoi_scaled_average H d (m₄*a) k₁ _

end
end ArtinMatthews
