module

public import ArtinMatthews.MarkedTypeIISharedMajorFinite
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

/-! Exact label restrictions and the fixed character on a scalar pair.
The original support filters can be kept either on the pair carrier or
as factors in the summand. -/
namespace ArtinMatthews
noncomputable section
open Finset
open scoped ComplexConjugate

variable {J : Type*} [Fintype J] (P : J → Finset ℕ)
  (L : Finset (ℕ×ℕ)) (E : (ℕ×ℕ) → Prop) [DecidablePred E]
  (S T N : Finset ℕ) (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q Y : ℝ)
  (α β : ℕ → ℂ) (G : (ℕ×ℕ) → (ℕ×ℕ) → (ℕ×ℕ) → ℂ)

theorem markedTypeIIScalarMajorOn_filter :
    markedTypeIIScalarMajorOn P (L.filter E) S T N η ψ Q Y α β G =
      markedTypeIIScalarMajorOn P L S T N η ψ Q Y α β
        (fun z v w => if E z then G z v w else 0) := by
  unfold markedTypeIIScalarMajorOn
  rw [sum_filter]
  apply congrArg (fun t : ℂ => (markedMajorLabelMass P:ℂ)^2*t)
  apply sum_congr rfl
  intro z _
  by_cases hz : E z
  · simp only [ite_eq_left hz]
  · simp only [ite_eq_right hz,zero_mul,sum_const_zero]

theorem markedTypeIIScalarMajorOn_filtered_dyad
    (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4) :
    markedTypeIIScalarMajorOn P ((markedMajorLabelSet P×ˢmarkedMajorLabelSet P).filter E)
      S T N η ψ Q Y α β G =
    markedTypeIIScalarMajorOn P ((markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter E)
      S T N η ψ Q Y α β G := by
  rw [markedTypeIIScalarMajorOn_filter,markedTypeIIScalarMajorOn_filter]
  exact markedTypeIIScalarMajorOn_dyad P S T N η ψ Q Y hY hη α β _

omit [Fintype J] in
theorem markedTypeIIScalarMajorTerm_character {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (b a : ℕ) (v w : ℕ×ℕ) :
    markedTypeIIScalarMajorTerm η ψ Q Y (fun m => ξ (m:ℕ)*α m) (fun n => ξ (n:ℕ)*β n) b a v w =
      (ξ (v.1*v.2:ℕ)*conj (ξ (w.1*w.2:ℕ)))*
        markedTypeIIScalarMajorTerm η ψ Q Y α β b a v w := by
  dsimp only [markedTypeIIScalarMajorTerm]
  simp only [Nat.cast_mul,map_mul]
  ring

end
end ArtinMatthews
