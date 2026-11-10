module

public import ArtinMatthews.MarkedMajorLabelSupportedEndpoint
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact zero-cutoff removal for the original finite source, with an arbitrary
bilateral kernel. No analytic or support bounds are needed. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem markedMajorSupported_weighted_sum {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ) (K : ℕ×(ℕ×ℕ) → ℂ) :
    (∑ z ∈ markedMajorSupportedTripleSet bands cutoff Y u v l r,
      markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*K z) =
    ∑ z ∈ markedMajorLabelTripleSet bands u v l r,
      markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*K z := by
  classical
  apply sum_subset (filter_subset _ _)
  intro z hz hznot
  have hz0 : cutoff ((z.1:ℝ)/Y)=0 := by
    by_contra h
    exact hznot (mem_filter.mpr ⟨hz,h⟩)
  simp only [markedMajorLabelTripleCoefficient,markedMajorLabelWeight,hz0,zero_mul]

theorem markedMajorSupported_conjugate_weighted_sum {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ) (K : ℕ×(ℕ×ℕ) → ℂ) :
    (∑ z ∈ markedMajorSupportedTripleSet bands cutoff Y u v l r,
      markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β z*K z) =
    ∑ z ∈ markedMajorLabelTripleSet bands u v l r,
      markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β z*K z := by
  simp only [markedMajorLabelConjugateTripleCoefficient_eq]
  exact markedMajorSupported_weighted_sum bands cutoff χb θ Y χ W (-modulation) u v l r β K

theorem markedMajorSupported_bilateral_sum {J J' : Type*} [Fintype J] [Fintype J']
    (bands : J → Finset ℕ) (bands' : J' → Finset ℕ) (cutoff : ℝ → ℂ)
    {k q k' q' : ℕ} (χb : DirichletCharacter ℂ k) (χb' : DirichletCharacter ℂ k')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (θ θ' Y W modulation modulation' u v u' v' : ℝ)
    (l r l' r' : ℕ) (β β' : ℕ → ℂ) (K : (ℕ×(ℕ×ℕ)) → (ℕ×(ℕ×ℕ)) → ℂ) :
    (∑ z ∈ markedMajorSupportedTripleSet bands cutoff Y u v l r,
      ∑ z' ∈ markedMajorSupportedTripleSet bands' cutoff Y u' v' l' r',
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff χb' θ' Y χ' W modulation' β' z')*K z z') =
    ∑ z ∈ markedMajorLabelTripleSet bands u v l r,
      ∑ z' ∈ markedMajorLabelTripleSet bands' u' v' l' r',
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff χb' θ' Y χ' W modulation' β' z')*K z z' := by
  simp_rw [mul_assoc,← mul_sum]
  simp_rw [markedMajorSupported_conjugate_weighted_sum]
  exact markedMajorSupported_weighted_sum bands cutoff χb θ Y χ W modulation u v l r β _

end
end ArtinMatthews
