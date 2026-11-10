module

public import ArtinMatthews.GiantTwoSidedRootLabelEquiv
public import ArtinMatthews.GiantTwoSidedRootMargin
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

/-! The actual root margin removes the auxiliary finite-slice tests
from the label parametrization. Distinctness, copy/ban compatibility
and every active congruence remain in the exact finite root sum. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

structure GiantTwoSidedRootAdmissible {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    {I : Finset ℕ} (d : GiantTwoSidedRootLabelData (P:=P) k ell n I) : Prop where
  distinct : ∀ v,MarkedPhysicalMarkingDistinct (d.2 v)
  compatible : ∀ i,GiantTwoSidedLabelCompatible (C i)
    (giantTwoSidedPermuteLabels (π i) (d.2 i.castSucc))
    (giantTwoSidedPermuteLabels (τ i) (d.2 i.succ)) (aux i)
  divides : ∀ v j l,(d.2 v j l:ℤ)∣giantTwoSidedRootLabelPosition C π aux step d v

theorem giantCandidateRootAdmissible_iff (k : ℕ) (C₂ : ℝ) {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let n := giantTwoSidedSourceMomentLength x
      ∀ (ell : ℕ) (C : Fin n → S → Finset (Fin k))
        (π τ : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ)≤(Real.log x)^C₂) → ∀ X : ℝ,x^γ≤X →
        ∀ d : GiantTwoSidedRootLabelData (P:=P) k ell n (giantTwoSidedRootInterval X),
          GiantTwoSidedRootLabelCondition C π τ aux step (giantTwoSidedRootSlice X) d ↔
            GiantTwoSidedRootAdmissible C π τ aux step d := by
  filter_upwards [giantCandidateLabelRoot_margin k C₂ hγ] with x hm
  intro S
  dsimp only
  intro ell C π τ aux step hstep X hX d
  constructor
  · intro h
    exact ⟨h.distinct,h.compatible,h.divides⟩
  · intro h
    have hg := hm S ell C d.2 π aux step hstep X hX d.1.val d.1.property
    exact ⟨h.distinct,h.compatible,fun v => (hg v).1.le,fun v => (hg v).2,h.divides⟩

theorem giantCandidatePhysicalPath_root_sum {A : Type*} [AddCommMonoid A]
    (k : ℕ) (C₂ : ℝ) {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let n := giantTwoSidedSourceMomentLength x
      ∀ (ell : ℕ) (C : Fin n → S → Finset (Fin k))
        (π τ : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ)≤(Real.log x)^C₂) → ∀ X : ℝ,x^γ≤X →
        ∀ f : GiantTwoSidedRootLabelData (P:=P) k ell n (giantTwoSidedRootInterval X) → A,
          (∑ s : GiantTwoSidedPhysicalPath C π τ aux step (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X),
            f (giantTwoSidedRootLabel_encode s).val) =
          ∑ r : ↥(giantTwoSidedRootInterval X),∑ labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell),
            if GiantTwoSidedRootAdmissible C π τ aux step (r,labels) then f (r,labels) else 0 := by
  filter_upwards [giantCandidateRootAdmissible_iff k C₂ hγ] with x hc
  intro S
  dsimp only
  intro ell C π τ aux step hstep X hX f
  rw [giantTwoSidedRootLabel_sum C π τ aux step (giantTwoSidedRootInterval X)
    (giantTwoSidedRootSlice X) (fun d => f d.val)]
  let valid (d : GiantTwoSidedRootLabelData (P:=fun i : S => giantCandidateGroup x i.val) k ell
      (giantTwoSidedSourceMomentLength x) (giantTwoSidedRootInterval X)) :=
    GiantTwoSidedRootLabelCondition C π τ aux step (giantTwoSidedRootSlice X) d
  have hs := Finset.sum_subtype (p:=valid) (F:=inferInstance) (univ.filter valid) (by simp) f
  rw [← hs,sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro labels _
  simp only [valid,hc S ell C π τ aux step hstep X hX (r,labels)]

end
end ArtinMatthews
