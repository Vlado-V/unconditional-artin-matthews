module

public import ArtinMatthews.MarkedMajorArcConjugate
public import ArtinMatthews.MarkedSparsePhaseKernel
public import ArtinMatthews.MarkedMajorArcIsolatedCancellation
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

/-! The conjugated endpoint has the same actual isolated-prime energy. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

 theorem marked_major_isolated_prime_conjugate_cancellation
    (c C₁ C₂ d a η τ C b K σ b₀ D P : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hd : 0 < d)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C)
    (hσ : 0 ≤ σ) (hb₀ : 0 ≤ b₀) (hD : 0 ≤ D) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (Y T H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
        1 < Y → c*L^(1/(10:ℝ)) ≤ Real.log Y →
        Real.log Y ≤ C₁*L^(1/(5:ℝ)) → 1 < T → Real.log T ≤ C₂*L →
        T ≤ K*Real.exp L*L^b → Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v →
        v ≤ 2*H → v ≤ Real.exp (η*L) → Real.exp (d*L) ≤ U →
        U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → H*U ≤ Real.exp (σ*L) → T/(H*U) ≤ L^b₀ →
        (∀ n ∈ Icc l r, ‖β n‖ ≤ L^D) →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation : ℝ),
          (q:ℝ) ≤ L^a → |modulation| ≤ L^C →
          ∀ (k : ℕ) (χp : DirichletCharacter ℂ k) (ξ : ℝ) (S : Finset ℕ),
            (∀ p ∈ S, p.Prime) → (∀ p ∈ S, (p:ℝ) ≤ 2*Y) →
            (∫ t in Set.Icc (-T) T,
              ‖markedPrimePolynomial S Y χp ξ t*
                markedMajorConjugateCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v*
                markedDyadicPolynomial l r U β t‖^2) ≤ L^(-P) := by
  filter_upwards [marked_major_isolated_prime_cancellation c C₁ C₂ d a η τ C b K σ b₀ D P
    hc hC₁ hC₂ hd ha hη hτ hC hσ hb₀ hD hP] with L hL
  intro Y T H u v U l r β hY hYlo hYhi hT hTlog hTupper hH hHu huv hvH hvhi hU hl hr hHU hratio hβ
    q _ χ modulation hq hmod k χp ξ S hS hScap
  simp only [marked_conjugate_centered_sum_eq]
  exact hL Y T H u v U l r β hY hYlo hYhi hT hTlog hTupper hH hHu huv hvH hvhi hU hl hr hHU hratio hβ
    q χ (-modulation) hq (by simpa only [abs_neg] using hmod) k χp ξ S hS hScap

end ArtinMatthews
