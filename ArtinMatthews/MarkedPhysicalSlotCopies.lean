module

public import ArtinMatthews.MarkedPhysicalHilbertMatrix
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

/-! Exact copies in each GSTSG entry: two independent literal slot
permutations, their actual probability, and the original good masks. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedPhysicalSlotMatrix_star {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (s t : MarkedPhysicalState P M Z) :
    star (markedPhysicalSlotMatrix P M Z s t)=markedPhysicalSlotMatrix P M Z s t := by
  simp only [markedPhysicalSlotMatrix,star_mul,star_inv₀,star_natCast,star_sum,
    apply_ite star,star_one,star_zero]
  ring

theorem markedPhysicalSlotMatrix_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (s t : MarkedPhysicalState P M Z) :
    markedPhysicalSlotMatrix P M Z s t=markedPhysicalSlotMatrix P M Z t s := by
  have h := congrFun (congrFun (markedPhysicalSlotMatrix_isHermitian P M Z).eq s) t
  change star (markedPhysicalSlotMatrix P M Z t s)=markedPhysicalSlotMatrix P M Z s t at h
  rw [markedPhysicalSlotMatrix_star] at h
  exact h.symm

theorem markedPhysicalSlotMatrix_mul_left {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (T : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ)
    (s t : MarkedPhysicalState P M Z) :
    (markedPhysicalSlotMatrix P M Z*T) s t =
      (Fintype.card (J → Equiv.Perm (Fin M)):ℂ)⁻¹ *
        ∑ σ : J → Equiv.Perm (Fin M), T (markedPhysicalSlotEquiv P M Z σ s) t :=
  markedPhysicalSlotMatrix_action P M Z (fun u => T u t) s

theorem markedPhysicalSlotMatrix_mul_right {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (T : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ)
    (s t : MarkedPhysicalState P M Z) :
    (T*markedPhysicalSlotMatrix P M Z) s t =
      (Fintype.card (J → Equiv.Perm (Fin M)):ℂ)⁻¹ *
        ∑ σ : J → Equiv.Perm (Fin M), T s (markedPhysicalSlotEquiv P M Z σ t) := by
  change (∑ u,T s u*markedPhysicalSlotMatrix P M Z u t)=_
  simp_rw [markedPhysicalSlotMatrix_symmetric P M Z _ t]
  have h := markedPhysicalSlotMatrix_action P M Z (fun u => T s u) t
  change (∑ u,markedPhysicalSlotMatrix P M Z t u*T s u)=_ at h
  simpa only [mul_comm] using h

theorem markedPhysicalSlotMatrix_double_average {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (T : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ)
    (s t : MarkedPhysicalState P M Z) :
    (markedPhysicalSlotMatrix P M Z*T*markedPhysicalSlotMatrix P M Z) s t =
      ((Fintype.card (J → Equiv.Perm (Fin M)):ℂ)⁻¹)^2 *
        ∑ σ : J → Equiv.Perm (Fin M), ∑ τ : J → Equiv.Perm (Fin M),
          T (markedPhysicalSlotEquiv P M Z σ s) (markedPhysicalSlotEquiv P M Z τ t) := by
  rw [markedPhysicalSlotMatrix_mul_right]
  simp_rw [markedPhysicalSlotMatrix_mul_left]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem markedPhysicalRestrictedMatrix_copies
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G s t =
      (if G s then (1:ℂ) else 0)*(if G t then (1:ℂ) else 0)*
        ((Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℂ)⁻¹)^2 *
          ∑ σ : J → Equiv.Perm (Fin (pads+1)), ∑ τ : J → Equiv.Perm (Fin (pads+1)),
            markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q
              (markedPhysicalSlotEquiv P (pads+1) Z σ s)
              (markedPhysicalSlotEquiv P (pads+1) Z τ t) := by
  have he : markedPhysicalGoodMatrix G*markedPhysicalSlotMatrix P (pads+1) Z*
      markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q*
      markedPhysicalSlotMatrix P (pads+1) Z*markedPhysicalGoodMatrix G =
    markedPhysicalGoodMatrix G*(markedPhysicalSlotMatrix P (pads+1) Z*
      markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q*
      markedPhysicalSlotMatrix P (pads+1) Z)*markedPhysicalGoodMatrix G := by
    simp only [Matrix.mul_assoc]
  calc
    _ = (markedPhysicalGoodMatrix G*(markedPhysicalSlotMatrix P (pads+1) Z*
      markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q*
      markedPhysicalSlotMatrix P (pads+1) Z)*markedPhysicalGoodMatrix G) s t :=
        congrArg (fun B : Matrix (MarkedPhysicalState P (pads+1) Z)
          (MarkedPhysicalState P (pads+1) Z) ℂ => B s t) he
    _ = _ := by
      simp only [markedPhysicalGoodMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal]
      rw [markedPhysicalSlotMatrix_double_average]
      ring

end
end ArtinMatthews
