module

public import ArtinMatthews.RationalPhaseCharacters
public import ArtinMatthews.DirichletPrimitiveExpansion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace ArtinMatthews

open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {r Q : ℕ} [NeZero r]

def rationalPhasePrimitiveCoefficient (hQr : r ≤ Q) (u : ℤ)
    (ψ : IdealPrimitiveCharacters Q) : ℂ :=
  dirichletPrimitiveCoefficient hQr (rationalPhaseCharacterCoefficient r u) ψ

theorem rationalPhasePrimitiveCoefficient_l1_le (hQr : r ≤ Q) (u : ℤ) :
    (∑ ψ : IdealPrimitiveCharacters Q, ‖rationalPhasePrimitiveCoefficient hQr u ψ‖) ≤
      Real.sqrt (r.totient : ℝ) :=
  (dirichletPrimitiveCoefficient_l1_le hQr _).trans
    (rationalPhaseCharacterCoefficient_l1_le r u)

theorem rationalPhase_bilinear_primitive_sum (hQr : r ≤ Q) (u : ℤ)
    (n m : ℕ) (hn : n.Coprime r) (hm : m.Coprime r) :
    (Real.fourierChar ((u : ℝ) * (n : ℝ) * (m : ℝ) / (r : ℝ)) : ℂ) =
      ∑ ψ : IdealPrimitiveCharacters Q,
        rationalPhasePrimitiveCoefficient hQr u ψ *
          idealPrimitiveCharacterValue ψ n * idealPrimitiveCharacterValue ψ m := by
  rw [rationalPhase_bilinear_character_sum r u n m hn hm]
  symm
  have h := dirichletPrimitiveCoefficient_sum hQr
    (rationalPhaseCharacterCoefficient r u)
    (fun ψ => idealPrimitiveCharacterValue ψ n * idealPrimitiveCharacterValue ψ m)
  simpa only [rationalPhasePrimitiveCoefficient, mul_assoc,
    dirichletPrimitiveRepresentative_value hQr _ n hn,
    dirichletPrimitiveRepresentative_value hQr _ m hm] using h

theorem rationalPhase_primitive_expansion (hQr : r ≤ Q) (u : ℤ) :
    ∃ a : IdealPrimitiveCharacters Q → ℂ,
      (∑ ψ : IdealPrimitiveCharacters Q, ‖a ψ‖) ≤ Real.sqrt (r.totient : ℝ) ∧
      ∀ n m : ℕ, n.Coprime r → m.Coprime r →
        (Real.fourierChar ((u : ℝ) * (n : ℝ) * (m : ℝ) / (r : ℝ)) : ℂ) =
          ∑ ψ : IdealPrimitiveCharacters Q,
            a ψ * idealPrimitiveCharacterValue ψ n * idealPrimitiveCharacterValue ψ m :=
  ⟨rationalPhasePrimitiveCoefficient hQr u,
    rationalPhasePrimitiveCoefficient_l1_le hQr u,
    rationalPhase_bilinear_primitive_sum hQr u⟩

end
end ArtinMatthews
