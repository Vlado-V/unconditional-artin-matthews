module

public import ArtinMatthews.CircleShiftedSum
public import ArtinMatthews.CircleSourceDetector
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! Direct finite-circle approximation for the original shifted pairs
`(m1*n+1,m2*n+1)` of the manuscript, with its exact gcd congruence. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem circleShifted_original_approximation (m1 m2 K1 K2 : ℕ)
    (hm1 : 0 < m1) (hs1 : Squarefree m1)
    (a : ℕ×ℕ → ℂ) (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) (hΛ : 0<circleNormalizer Q ω) :
    let d := m1.gcd m2
    let m3 := m1/d
    let m4 := m2/d
    ‖(∑ k∈((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)).filter
        (fun k => (d : ℤ)∣((k.1 : ℤ)-1)),
        a k*circleDetector Q ω (circleShiftedFrequency m3 m4 k)) -
      (∑ n∈(Finset.range (K1+1)).filter (fun n => m1*n+1≤K1 ∧ m2*n+1≤K2),
        a (m1*n+1,m2*n+1))‖ ≤
      (∑ k∈(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2), ‖a k‖) *
        (circleWeightMass Q ω*((m4*K1+m3*K2 : ℕ) : ℝ)^2/circleNormalizer Q ω) := by
  classical
  intro d m3 m4
  have hd : 0<d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m1 m2) hm1
  have h1 : d*m3=m1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left m1 m2)
  have h2 : d*m4=m2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right m1 m2)
  have hm3 : 0 < m3 := by nlinarith
  have h34 : m3.Coprime m4 := Nat.coprime_div_gcd_div_gcd hd
  have h3d : m3.Coprime d := (Nat.coprime_of_squarefree_mul (h1 ▸ hs1)).symm
  have hreindex := circleShifted_sum d m3 m4 K1 K2 hd hm3 h34 h3d a
  simp only [circleShiftedPairs,circleShiftedIndices,h1,h2] at hreindex
  have hb := circleDetector_finite_congruence_approximation
    ((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)) a (circleShiftedFrequency m3 m4)
    (fun k => (k.1 : ℤ)-1) d Q ω hω hΛ (m4*K1+m3*K2)
    (fun k hk => circleShiftedFrequency_bound m3 m4 K1 K2 hk)
  rw [hreindex] at hb
  exact hb

end ArtinMatthews
