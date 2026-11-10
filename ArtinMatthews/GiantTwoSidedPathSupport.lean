module

public import ArtinMatthews.GiantTwoSidedRootLabelData
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Restricting the original finite path sum to supported edges is
exact: every excluded path has a zero factor in the actual kernel. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedPhysicalPath_product_zero {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    {Z : Finset ℕ} (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z)
    (h : ¬∀ i,GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) :
    (∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i))=0 := by
  push Not at h
  obtain ⟨i,hi⟩ := h
  apply prod_eq_zero (mem_univ i)
  exact ite_eq_right hi

theorem giantTwoSidedPhysicalPath_sum_support {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    (I Z : Finset ℕ) (F : (Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z) → ℂ) :
    (∑ s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z,
      if (s 0).val.1.val∈I then F s*
        (∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
          (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
          (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) else 0) =
      ∑ s : GiantTwoSidedPhysicalPath C π τ aux step I Z,F s.val*
        (∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
          (giantTwoSidedEndpointPermute (π i) (s.val i.castSucc))
          (giantTwoSidedEndpointPermute (τ i) (s.val i.succ)) (aux i)) := by
  let g (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z) := F s*
    ∏ i : Fin n,giantTwoSidedPatternPhysicalCoefficient (step i) q (ζ i) (K i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)
  let valid := GiantTwoSidedPhysicalPathCondition C π τ aux step I Z
  have hs := Finset.sum_subtype (p:=valid) (F:=inferInstance) (univ.filter valid) (by simp) g
  rw [← hs,sum_filter]
  apply sum_congr rfl
  intro s _
  have hc : valid s ↔ (s 0).val.1.val∈I ∧ ∀ i,GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i) :=
    ⟨fun h => ⟨h.root_mem,h.edges⟩,fun h => ⟨h.1,h.2⟩⟩
  change (if _ then g s else 0)=(if valid s then g s else 0)
  rw [hc]
  by_cases hr : (s 0).val.1.val∈I
  · by_cases he : ∀ i,GiantTwoSidedPatternCondition (C i) (step i)
        (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
        (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)
    · rw [ite_eq_left hr,ite_eq_left (And.intro hr he)]
    · have hg : g s=0 := by
        dsimp only [g]
        rw [giantTwoSidedPhysicalPath_product_zero π τ aux step q ζ K s he,mul_zero]
      rw [ite_eq_left hr,ite_eq_right (fun hh => he hh.2),hg]
  · rw [ite_eq_right hr,ite_eq_right (fun hh => hr hh.1)]

end
end ArtinMatthews
