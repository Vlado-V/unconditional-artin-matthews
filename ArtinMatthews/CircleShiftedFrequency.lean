module

public import ArtinMatthews.CircleDetector
public import ArtinMatthews.CircleFiniteApproximation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Lemmas
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual integer frequency of the shifted-convolution source equation. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def circleShiftedFrequency (m3 m4 : ℕ) (k : ℕ×ℕ) : ℤ :=
  (m4 : ℤ)*((k.1 : ℤ)-1)-(m3 : ℤ)*((k.2 : ℤ)-1)

theorem circleShiftedFrequency_bound (m3 m4 K1 K2 : ℕ) {k : ℕ×ℕ}
    (hk : k ∈ (Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)) :
    (circleShiftedFrequency m3 m4 k).natAbs ≤ m4*K1+m3*K2 := by
  obtain ⟨hk1,hk2⟩ := Finset.mem_product.mp hk
  obtain ⟨hl1,hu1⟩ := Finset.mem_Icc.mp hk1
  obtain ⟨hl2,hu2⟩ := Finset.mem_Icc.mp hk2
  have h1 : m4*(k.1-1) ≤ m4*K1+m3*K2 :=
    (Nat.mul_le_mul_left m4 ((Nat.sub_le k.1 1).trans hu1)).trans (Nat.le_add_right _ _)
  have h2 : m3*(k.2-1) ≤ m4*K1+m3*K2 :=
    (Nat.mul_le_mul_left m3 ((Nat.sub_le k.2 1).trans hu2)).trans (Nat.le_add_left _ _)
  simpa only [circleShiftedFrequency,Nat.cast_mul,Nat.cast_sub hl1,Nat.cast_sub hl2,
    Nat.cast_one] using Int.natAbs_coe_sub_coe_le_of_le h1 h2

theorem circleShifted_finite_approximation (m3 m4 K1 K2 : ℕ)
    (a : ℕ×ℕ → ℂ) (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) (hΛ : 0<circleNormalizer Q ω) :
    ‖(∑ k∈(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2),
        a k*circleDetector Q ω (circleShiftedFrequency m3 m4 k)) -
      (∑ k∈((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)).filter
        (fun k => circleShiftedFrequency m3 m4 k=0), a k)‖ ≤
      (∑ k∈(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2), ‖a k‖) *
        (circleWeightMass Q ω*((m4*K1+m3*K2 : ℕ) : ℝ)^2/circleNormalizer Q ω) :=
  circleDetector_finite_approximation _ a (circleShiftedFrequency m3 m4) Q ω hω hΛ _
    (fun _ hk => circleShiftedFrequency_bound m3 m4 K1 K2 hk)

end ArtinMatthews
