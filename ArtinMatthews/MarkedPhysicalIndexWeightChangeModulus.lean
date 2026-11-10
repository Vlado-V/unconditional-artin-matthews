module

public import ArtinMatthews.MarkedPhysicalIndexMonomialTransport
public import ArtinMatthews.MarkedPhysicalRootChangeModulus
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

/-! The source monomials and Bonferroni polynomials use the same
canonical integer root at every selected modulus. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCanonicalRootChangeModulus_point
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) :
    (markedPhysicalCanonicalRootChangeModulus S T hA hC r).2.1=r.2.1 := by
  have hp := markedPhysicalCanonicalRootChangeModulus_position S T hA hC r
  have hc := congrArg Prod.fst (markedPhysicalCanonicalRootChangeModulus_completion S T hA hC r)
  have hu := congrArg Prod.fst hp
  have hv := congrArg Prod.snd hp
  let r' := markedPhysicalCanonicalRootChangeModulus S T hA hC r
  change r'.2.1=r.2.1
  have hpoint : ∀ (p q : Σ _u : ℤ,ℤ × ℤ),p.1=q.1 → p.2.1=q.2.1 → p.2.2=q.2.2 → p=q := by
    rintro ⟨u,c,v⟩ ⟨u',c',v'⟩ hu hc hv
    dsimp only at hu hc hv
    subst u'
    subst c'
    subst v'
    rfl
  exact hpoint _ _ hu hc hv

theorem markedPhysicalIndexLiftedPosition_changeModulus
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex P M n R)
    (S T : ℕ) [NeZero S] [NeZero T] {U V : ℝ} (hU : 1 < U) (hV : 1 < V)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) :
    markedPhysicalIndexLiftedPosition i (markedPhysicalCanonicalRootChangeModulus S T hU hV r)=
      markedPhysicalIndexLiftedPosition i r := by
  unfold markedPhysicalIndexLiftedPosition
  rw [markedPhysicalCanonicalRootChangeModulus_position,markedPhysicalCanonicalRootChangeModulus_completion]

theorem markedPhysicalIndexMonomialWeight_changeModulus
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ) {n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1 ≤ R) (q : ℝ) (T₀ : Finset ℕ)
    (S T : ℕ) [NeZero S] [NeZero T] (hU : 1 < U) (hV : 1 < V)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) :
    markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T₀
        (markedPhysicalCanonicalRootChangeModulus S T hU hV r)=
      markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T₀ r := by
  unfold markedPhysicalIndexMonomialWeight MarkedPhysicalIndexRootValid
  rw [markedPhysicalIndexLiftedPosition_changeModulus,
    markedPhysicalCanonicalRootChangeModulus_point]

theorem markedPhysicalIndexMonomialWeight_sum_changeModulus
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ) {n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1 ≤ R) (q : ℝ) (T₀ : Finset ℕ)
    (S T : ℕ) [NeZero S] [NeZero T] (hU : 1 < U) (hV : 1 < V) :
    (∑ r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V),
      markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T₀ r)=
    ∑ r : MarkedPhysicalCanonicalRoot T U (16*U) V (2*V),
      markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T₀ r := by
  calc
    _ = ∑ r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V),
        markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T₀
          (markedPhysicalCanonicalRootChangeModulus S T hU hV r) := by
      simp only [markedPhysicalIndexMonomialWeight_changeModulus]
    _ = _ := Equiv.sum_comp (markedPhysicalCanonicalRootChangeModulus S T hU hV)
      (fun r : MarkedPhysicalCanonicalRoot T U (16*U) V (2*V) =>
        markedPhysicalIndexMonomialWeight e x d₀ Y U V i hR q T₀ r)

end
end ArtinMatthews
