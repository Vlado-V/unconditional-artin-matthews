module

public import ArtinMatthews.MarkedMajorArcPaperSource
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
public import Mathlib.Tactic.Basify
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

/-! Selecting a distinguished prime band preserves the actual label set,
normalizer and literal sixfold determinant sum exactly. -/
namespace ArtinMatthews
open Finset

 theorem markedMajorLabelSet_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : J → Finset ℕ) :
    markedMajorLabelSet (fun i => P (e i))=markedMajorLabelSet P := by
  classical
  let E := Equiv.piCongrLeft (fun j => ↥(P j)) e
  have hp (t : (i : I) → ↥(P (e i))) :
      markedPrimeBandProduct P (E t)=markedPrimeBandProduct (fun i => P (e i)) t := by
    unfold markedPrimeBandProduct
    rw [← e.prod_comp (fun j => (E t j:ℕ))]
    apply prod_congr rfl
    intro i _
    rw [Equiv.piCongrLeft_apply_apply]
  ext n
  simp only [markedMajorLabelSet,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨E t,hp t⟩
  · rintro ⟨t,rfl⟩
    refine ⟨E.symm t,?_⟩
    rw [← hp,E.apply_symm_apply]

 theorem markedMajorLabelMass_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : J → Finset ℕ) :
    markedMajorLabelMass (fun i => P (e i))=markedMajorLabelMass P :=
  e.prod_comp (fun j => (bandReciprocalMass (P j))⁻¹)

 theorem markedMajorDeterminantPaperSum_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : J → Finset ℕ) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ) :
    markedMajorDeterminantPaperSum (fun i => P (e i)) cutoff ψ Q Y W modulation u v l r β =
      markedMajorDeterminantPaperSum P cutoff ψ Q Y W modulation u v l r β := by
  simp only [markedMajorDeterminantPaperSum,markedMajorLabelSet_reindex,markedMajorLabelMass_reindex]

end ArtinMatthews
