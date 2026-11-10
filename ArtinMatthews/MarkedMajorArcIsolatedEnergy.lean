module

public import ArtinMatthews.MarkedSparsePhaseKernel
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.MarkedMajorArcEnergyCover
public import ArtinMatthews.MarkedMajorArcExceptionalCover
public import ArtinMatthews.MarkedSparsePhaseContinuity
public import ArtinMatthews.MarkedSparsePhaseInterval
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The literal shifted-prime isolated energy, with the actual exceptional
family and sparse supremum estimate instantiated. Product mean square and
long-coefficient inputs are explicit at this analytic assembly step. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

 theorem marked_isolated_prime_energy_of_mean
    (c C₁ C₂ A d : ℝ) (hc : 0 < c) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hA : 0 ≤ A) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (Y T U B m E : ℝ) (l r : ℕ) (a : ℕ → ℂ) (M : ℝ → ℂ),
        1 < Y → c*X^(1/(10:ℝ)) ≤ Real.log Y →
        Real.log Y ≤ C₁*X^(1/(5:ℝ)) → 1 < T → Real.log T ≤ C₂*X →
        Real.exp (d*X) ≤ U → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
        (∀ n ∈ Icc l r, ‖a n‖ ≤ B) → Continuous M →
        (∀ t ∈ Set.Icc (-T) T, ‖M t‖ ≤ m) →
        (∫ t in Set.Icc (-T) T, ‖M t*markedDyadicPolynomial l r U a t‖^2) ≤ E →
        ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ) (P : Finset ℕ),
          (∀ p ∈ P, p.Prime) → (∀ p ∈ P, (p:ℝ) ≤ 2*Y) →
          (∫ t in Set.Icc (-T) T,
            ‖markedPrimePolynomial P Y χ ξ t*M t*markedDyadicPolynomial l r U a t‖^2) ≤
              (X^(-A))^2*E+4*m^2*K*X*B^2 := by
  obtain ⟨K,hK,henergy⟩ := marked_sparse_frequency_unitInterval_energy c C₁ C₂ A d hc hC₁ hC₂ hA hd
  refine ⟨K,hK,?_⟩
  filter_upwards [henergy] with X he
  intro Y T U B m E l r a M hY hYlo hYhi hT hTlog hU hl hr ha hM hMb hmean
    k χ ξ P hP hPcap
  let F := markedPrimePolynomial P Y χ ξ
  let N := markedDyadicPolynomial l r U a
  let I := markedExceptionalUnitIntervals F T (X^(-A))
  have hs : (∑ z ∈ I, sSup ((fun t => ‖N t‖^2) '' Set.Icc (z:ℝ) ((z:ℝ)+1))) ≤ K*X*B^2 :=
    he Y T U B l r a hY hYlo hYhi hT hTlog hU hl hr ha k χ ξ P hP hPcap I
      (markedExceptionalUnitIntervals_witness F T (X^(-A)))
  have hh := marked_isolated_energy_cover F M N I T (X^(-A)) 2 m E (K*X*B^2)
    (markedPrimePolynomial_continuous P Y χ ξ) hM (markedDyadicPolynomial_continuous l r U a)
    (fun t _ => markedPrimePolynomial_norm_le_two P (by linarith) χ ξ t hP hPcap)
    hMb (fun t ht hPt => markedExceptionalUnitIntervals_cover F T (X^(-A)) t ht hPt.le)
    hmean hs
  exact hh.trans_eq (by ring)

end ArtinMatthews
