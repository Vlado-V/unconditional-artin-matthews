module

public import ArtinMatthews.MarkedMajorMellinEndpointSum
public import ArtinMatthews.MarkedSparsePrimeMoments
public import ArtinMatthews.MarkedMajorArcProductPolynomial
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

/-! Exact finite endpoint factorization on literal positive integer triples. -/
namespace ArtinMatthews
open Finset

theorem markedMajorEndpointPolynomial_nat_phase (n : ℕ) (t : ℝ) :
    Complex.exp (Complex.I*(t:ℂ)*(Real.log (n:ℝ):ℂ)) = markedPrimePhase n t := by
  unfold markedPrimePhase
  congr 1
  push_cast
  ring

theorem markedMajorEndpointPolynomial_triple (S T R : Finset ℕ)
    (a b c : ℕ → ℂ) (hS : ∀ s ∈ S,0 < s) (hT : ∀ m ∈ T,0 < m)
    (hR : ∀ n ∈ R,0 < n) (t : ℝ) :
    markedMajorEndpointPolynomial (S×ˢ(T×ˢR))
      (fun z => a z.1*b z.2.1*c z.2.2)
      (fun z => ((z.1*z.2.1*z.2.2:ℕ):ℝ)) t =
      (∑ s ∈ S,a s*markedPrimePhase s t)*
      (∑ m ∈ T,b m*markedPrimePhase m t)*
      (∑ n ∈ R,c n*markedPrimePhase n t) := by
  unfold markedMajorEndpointPolynomial
  rw [sum_product]
  simp only [sum_product,markedMajorEndpointPolynomial_nat_phase]
  rw [sum_mul_sum]
  simp only [sum_mul]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [← markedPrimePhase_mul (Nat.mul_pos (hS s hs) (hT m hm)) (hR n hn),
    ← markedPrimePhase_mul (hS s hs) (hT m hm)]
  ring

end ArtinMatthews
