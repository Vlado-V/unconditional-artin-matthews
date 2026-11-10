module

public import ArtinMatthews.MarkedPhysicalMomentPaths
public import ArtinMatthews.MarkedPhysicalSlotCopies
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

/-! Fully literal slot-copy coefficients for the true alternating physical
moment. Reverse edges use the actual conjugate transposed coefficient. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
  (G : MarkedPhysicalState P (pads+1) Z → Prop)

local notation "State" => MarkedPhysicalState P (pads+1) Z
local notation "Slots" => J → Equiv.Perm (Fin (pads+1))
local notation "A" => markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G
local notation "T" => markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q

def markedPhysicalMomentEdgeCopy (j : ℕ) (s t : State) (c : Slots × Slots) : ℂ :=
  (if G s then (1:ℂ) else 0)*(if G t then (1:ℂ) else 0)*
    ((Fintype.card Slots:ℂ)⁻¹)^2 *
      (if j%2=0 then
        T (markedPhysicalSlotEquiv P (pads+1) Z c.1 s) (markedPhysicalSlotEquiv P (pads+1) Z c.2 t)
      else star (T (markedPhysicalSlotEquiv P (pads+1) Z c.1 t) (markedPhysicalSlotEquiv P (pads+1) Z c.2 s)))

theorem markedPhysicalAlternatingMatrix_copies (j : ℕ) (s t : State) :
    markedAlternatingMatrix A j s t=
      ∑ c : Slots × Slots, markedPhysicalMomentEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q G j s t c := by
  by_cases hj : j%2=0
  · rw [markedAlternatingMatrix,ite_eq_left hj,markedPhysicalRestrictedMatrix_copies]
    simp only [markedPhysicalMomentEdgeCopy,hj,ite_true,Fintype.sum_prod_type,Finset.mul_sum]
  · rw [markedAlternatingMatrix,ite_eq_right hj,Matrix.conjTranspose_apply,
      markedPhysicalRestrictedMatrix_copies]
    simp only [markedPhysicalMomentEdgeCopy,hj,ite_false,Fintype.sum_prod_type,
      star_mul,star_pow,star_inv₀,star_natCast,star_sum,apply_ite star,star_one,star_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    ring

theorem markedPhysicalMatrixPathWeight_copies (n j : ℕ) (p : Fin (n+1) → State) :
    markedMatrixPathWeight (markedAlternatingMatrix A) n j p =
      ∑ copies : Fin n → Slots × Slots, ∏ v : Fin n,
        markedPhysicalMomentEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q G
          (j+v.val) (p v.castSucc) (p v.succ) (copies v) := by
  rw [markedMatrixPathWeight_product]
  simp_rw [markedPhysicalAlternatingMatrix_copies]
  exact Fintype.prod_sum _

theorem markedPhysicalPositionMoment_copies (hV : ∀ j,0≤V j) (R : ℕ) :
    markedPhysicalPositionMoment P (pads+1) Z V A R =
      markedPhysicalMass V (pads+1) *
        (∑ p : MarkedPhysicalMomentPath P (pads+1) Z R,
          if (p 0).1.1=(p (Fin.last (2*R))).1.1 then
            ∑ copies : Fin (2*R) → Slots × Slots, ∏ v : Fin (2*R),
              markedPhysicalMomentEdgeCopy P hP V pads Z hZ ψ η d₀ Y Q q G
                v.val (p v.castSucc) (p v.succ) (copies v)
          else 0).re := by
  rw [markedPhysicalPositionMoment_paths P (pads+1) Z V hV A R]
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · simpa only [zero_add] using markedPhysicalMatrixPathWeight_copies
      P hP V pads Z hZ ψ η d₀ Y Q q G (2*R) 0 p
  · rfl

end
end ArtinMatthews
