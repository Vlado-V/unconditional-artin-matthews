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


set_option backward.privateInPublic true
@[expose] public section

/-! Encode a physical path by its original root and full ordered label
array. The inverse reconstructs every visited state from the signed
increments, giving a finite bijection with all slice guards retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedRootLabel_encode {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (s : GiantTwoSidedPhysicalPath C π τ aux step I Z) : GiantTwoSidedRootLabelPath C π τ aux step I Z := by
  let d : GiantTwoSidedRootLabelData (P:=P) k ell n I :=
    (⟨(s.val 0).val.1.val,s.property.root_mem⟩,fun v => (s.val v).val.2)
  have hpos (v : Fin (n+1)) : giantTwoSidedRootLabelPosition C π aux step d v =
      ((s.val v).val.1.val:ℤ) :=
    (giantTwoSidedPatternPath_position s.val π τ aux step s.property.edges v).symm
  refine ⟨d,⟨fun v => (s.val v).property.1,?_,?_,?_,?_⟩⟩
  · intro i
    exact ⟨(s.property.edges i).1,(s.property.edges i).2.2⟩
  · intro v
    rw [hpos]
    exact Int.natCast_nonneg _
  · intro v
    rw [hpos,Int.toNat_natCast]
    exact (s.val v).val.1.property
  · intro v j l
    rw [hpos]
    exact Int.natCast_dvd_natCast.mpr ((s.val v).property.2 j l)

theorem giantTwoSidedRootLabel_encode_position {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (s : GiantTwoSidedPhysicalPath C π τ aux step I Z) (v : Fin (n+1)) :
    giantTwoSidedRootLabelPosition C π aux step (giantTwoSidedRootLabel_encode s).val v =
      ((s.val v).val.1.val:ℤ) :=
  (giantTwoSidedPatternPath_position s.val π τ aux step s.property.edges v).symm

def giantTwoSidedRootLabel_decode {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (d : GiantTwoSidedRootLabelPath C π τ aux step I Z) : GiantTwoSidedPhysicalPath C π τ aux step I Z :=
  ⟨giantTwoSidedRootLabel_reconstruct d,giantTwoSidedRootLabel_reconstruct_condition d⟩

def giantTwoSidedRootLabelEquiv {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) (I Z : Finset ℕ) :
    GiantTwoSidedPhysicalPath C π τ aux step I Z ≃ GiantTwoSidedRootLabelPath C π τ aux step I Z where
  toFun := giantTwoSidedRootLabel_encode
  invFun := giantTwoSidedRootLabel_decode
  left_inv s := by
    apply Subtype.ext
    funext v
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Int.ofNat.inj
      exact (giantTwoSidedRootLabel_reconstruct_position (giantTwoSidedRootLabel_encode s) v).trans
        (giantTwoSidedRootLabel_encode_position s v)
    · rfl
  right_inv d := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Int.ofNat.inj
      change ((giantTwoSidedRootLabel_reconstruct d 0).val.1.val:ℤ)=(d.val.1.val:ℤ)
      rw [giantTwoSidedRootLabel_reconstruct_position,giantTwoSidedRootLabelPosition,
        giantTwoSidedPathOffset_zero,add_zero]
    · rfl

theorem giantTwoSidedRootLabel_sum {J A : Type*} [Fintype J] [DecidableEq J] [AddCommMonoid A]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) (I Z : Finset ℕ)
    (f : GiantTwoSidedRootLabelPath C π τ aux step I Z → A) :
    (∑ s : GiantTwoSidedPhysicalPath C π τ aux step I Z,f (giantTwoSidedRootLabel_encode s)) =
      ∑ d : GiantTwoSidedRootLabelPath C π τ aux step I Z,f d :=
  (giantTwoSidedRootLabelEquiv C π τ aux step I Z).sum_comp f

end
end ArtinMatthews
