module

public import ArtinMatthews.DoubleVoronoiDualAverage
public import ArtinMatthews.DoubleVoronoiResidueWeight
public import ArtinMatthews.KloostermanWeightedStationary
public import ArtinMatthews.DoubleVoronoiCompleteSum
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

/-! The full normalized double finite sum following the two Voronoi
transforms, with its exact complete Kloosterman sum and D-congruence. -/
namespace ArtinMatthews
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman
open OAI.Erdos970.ErdosKloosterman.PrimePower
noncomputable section
attribute [local instance] Classical.decEq

/-- Literal normalized sum over both the circle numerator and the
congruence parameter equals the weighted complete Kloosterman sum. -/
theorem doubleVoronoi_average_eq_weighted (H d : ℕ) [NeZero H] [NeZero d]
    (hdH : d∣H) (v₃ v₄ : (ZMod (H*d))ˣ) (k₁ k₂ : ZMod (H*d)) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d,
      ZMod.stdAddChar (doubleVoronoiDualPhase H d hdH v₃ v₄ a k₁ k₂ j)) / (d : ℂ) =
    weightedKloosterman ZMod.stdAddChar
      (doubleVoronoiResidueWeight (ZMod.castHom (dvd_mul_left d H) (ZMod d))
        (v₄ : ZMod (H*d)) k₁)
      ((v₃ : ZMod (H*d))-(v₄ : ZMod (H*d)))
      ((↑(v₃*v₄)⁻¹ : ZMod (H*d))*((v₄ : ZMod (H*d))*k₂-(v₃ : ZMod (H*d))*k₁)) := by
  rw [Finset.sum_div]
  unfold weightedKloosterman
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [doubleVoronoi_dual_average H d hdH]
  have hunit : (ZMod.unitsMap (dvd_mul_left d H) (v₄*a) : ZMod d) =
      (ZMod.castHom (dvd_mul_left d H) (ZMod d)) (v₄ : ZMod (H*d))*
      (ZMod.castHom (dvd_mul_left d H) (ZMod d)) (a : ZMod (H*d)) := by
    change (ZMod.castHom (dvd_mul_left d H) (ZMod d)) (↑(v₄*a) : ZMod (H*d)) = _
    rw [Units.val_mul, map_mul]
  unfold doubleVoronoiResidueWeight
  simp only [hunit, reduction]
  ring

/-- Exact full finite arithmetic of (5.9), before any analytic estimate. -/
theorem doubleVoronoi_complete_average (H d r : ℕ) [NeZero H] [NeZero d]
    (hdH : d∣H) (hQ : (d*r)^2∣H*d) (hr : r≠0)
    (m₃ m₄ k₁ k₂ A₀ : ℤ)
    (hfactor : m₃-m₄=(r : ℤ)*A₀) (hcop : IsCoprime (d : ℤ) (m₃*A₀))
    (v₃ v₄ : (ZMod (H*d))ˣ)
    (h₃ : (v₃ : ZMod (H*d))=(m₃ : ZMod (H*d)))
    (h₄ : (v₄ : ZMod (H*d))=(m₄ : ZMod (H*d))) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d,
      ZMod.stdAddChar (doubleVoronoiDualPhase H d hdH v₃ v₄ a k₁ k₂ j)) / (d : ℂ) =
    (if Int.ModEq ((d : ℤ)*(r : ℤ)) (m₃^2*k₁) (m₄^2*k₂) then 1 else 0) *
      sum ZMod.stdAddChar ((v₃ : ZMod (H*d))-(v₄ : ZMod (H*d)))
        ((↑(v₃*v₄)⁻¹ : ZMod (H*d))*((v₄ : ZMod (H*d))*k₂-(v₃ : ZMod (H*d))*k₁)) := by
  rw [doubleVoronoi_average_eq_weighted H d hdH, h₄]
  simpa only [h₄] using doubleVoronoi_weighted_complete_sum
    (Nat.mul_pos (NeZero.pos H) (NeZero.pos d)) hQ hr m₃ m₄ k₁ k₂ A₀ hfactor hcop v₃ v₄ h₃ h₄

end
end ArtinMatthews
