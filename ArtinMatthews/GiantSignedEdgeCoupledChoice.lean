module

public import ArtinMatthews.GiantSignedEdgeCoupledPairing
public import ArtinMatthews.GiantSignedEdgeMoveExpansion
public import ArtinMatthews.GiantSignedEdgeSquare
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The paired row retains both divisibility bans on the original choices. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ} {t : B → ℕ}

private theorem move_norm_eq_real
    (ν : ∀ j, P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : B → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (d : ℤ) (D : ℕ) (a b : GiantSignedPrimeTuple P t)
    (m : GiantSignedMemory P) (c : GiantSignedEdgeChoice t m.1) :
    ‖giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D a b m c‖ =
      (∏ j, (V j)⁻¹ ^ (c.2.1 j).card) * giantSignedFreshPrimeRealMass ν c.2.1 b *
        if GiantSignedEdgeHits d m b c ∧ GiantSignedEdgePromotionBan D c.2.1 b then
          giantSignedPendingDamping ρ m *
            giantSignedPendingDamping ρ (giantSignedEdgeTarget d m a c)
        else 0 := by
  apply Complex.ofReal_injective
  rw [← giantSignedEdgeMoveCoefficient_eq_norm ν hν V hV hρ]
  unfold giantSignedEdgeMoveCoefficient giantSignedPromotionCharge
    giantSignedFreshPrimeMass giantSignedFreshPrimeRealMass
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow,
    Complex.ofReal_inv, apply_ite, Complex.ofReal_zero]
  split_ifs <;> rfl

theorem giantSignedEdgeCoupledApply_bothBans_choice_sum
    (ν : ∀ j, P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : B → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (d : ℤ) (D : ℕ) (F : GiantSignedEdgeCoupledTest P t ℝ)
    (a : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    giantSignedEdgeCoupledApply ν V ρ d
      (fun S T source target old out =>
        if GiantSignedEdgePromotionBan D S source ∧ GiantSignedEdgePromotionBan D T target then
          F S T source target old out else 0) a m =
      ∑ c : GiantSignedEdgeChoice t m.1, ∑ b : GiantSignedPrimeTuple P t,
        ‖giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D a b m c‖ *
          if GiantSignedEdgePromotionBan D c.1 a then
            F c.1 c.2.1 a b m (giantSignedEdgeTarget d m a c) else 0 := by
  unfold giantSignedEdgeCoupledApply GiantSignedEdgeChoice
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [move_norm_eq_real ν hν V hV hρ]
  by_cases hh : GiantSignedEdgeHits d m b ⟨S,T,e⟩ <;>
    by_cases hs : GiantSignedEdgePromotionBan D S a <;>
    by_cases ht : GiantSignedEdgePromotionBan D T b <;>
    simp [hh, hs, ht, mul_assoc]

end
end ArtinMatthews
