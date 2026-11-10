module

public import ArtinMatthews.MarkedMajorArcConjugate
public import ArtinMatthews.MarkedMajorArcHighCentered
public import ArtinMatthews.MarkedMajorArcLowCentered
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


set_option backward.privateInPublic true
@[expose] public section

/-! The complete major-arc long-coefficient estimate: all frequencies in
the original exponential-times-polynomial range, with actual prime/rough
centering, every character, modulation, and arbitrary dyadic subinterval. -/
namespace ArtinMatthews
open Filter
open scoped Topology

 theorem marked_major_long_coefficient (a η τ C b K P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation t H u v : ℝ),
        (q:ℝ) ≤ L^a → |modulation| ≤ L^C → |t| ≤ K*Real.exp L*L^b →
        Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*L) →
        ‖markedMajorCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v‖ ≤ L^(-P) := by
  obtain ⟨T,hT,hhigh⟩ := marked_major_high_centered_cancellation a η τ C b K P ha hη hτ hP
  filter_upwards [hhigh,marked_major_low_centered_cancellation a η τ C T P ha hη hτ hC hT.le hP]
    with L hhigh hlow
  intro q _ χ modulation t H u v hq hm ht hH hHu huv hvH hvhi
  by_cases hlo : L^T ≤ |t|
  · exact hhigh q χ modulation t H u v hq hm hlo ht hH hHu huv hvH hvhi
  · exact hlow q χ modulation t H u v hq hm (le_of_not_ge hlo) hH hHu huv hvH hvhi

/-- The same quantitative estimate for the literal conjugated coefficients.
Characters are arbitrary in both conclusions, so this also includes their
conjugates. -/
theorem marked_major_long_coefficient_and_conjugate (a η τ C b K P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation t H u v : ℝ),
        (q:ℝ) ≤ L^a → |modulation| ≤ L^C → |t| ≤ K*Real.exp L*L^b →
        Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*L) →
        ‖markedMajorCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v‖ ≤ L^(-P) ∧
        ‖markedMajorConjugateCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v‖ ≤ L^(-P) := by
  filter_upwards [marked_major_long_coefficient a η τ C b K P ha hη hτ hC hP]
    with L hL
  intro q _ χ modulation t H u v hq hm ht hH hHu huv hvH hvhi
  refine ⟨hL q χ modulation t H u v hq hm ht hH hHu huv hvH hvhi,?_⟩
  rw [marked_conjugate_centered_sum_eq]
  exact hL q χ (-modulation) t H u v hq (by simpa only [abs_neg] using hm)
    ht hH hHu huv hvH hvhi

end ArtinMatthews
