module

public import ArtinMatthews.MarkedPhysicalPathArrays
public import ArtinMatthews.MarkedPhysicalRootTargetReindex
public import ArtinMatthews.MarkedPhysicalFiniteTargetCoordinates
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

/-! Exact canonical-root and residue enumeration of a full position
array. The root is counted once; all remaining positions and repetitions
are preserved through the actual unimodular coordinate equivalence. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable

def markedPhysicalPositionPathExtend {Z : Finset (ℤ × ℤ)} {n : ℕ}
    (F : MarkedPhysicalPositionPath Z n → ℂ) (p : Fin (n+1) → ℤ × ℤ) : ℂ :=
  if h : ∀ v,p v∈Z then F (fun v => ⟨p v,h v⟩) else 0

theorem markedPhysicalPositionPathExtend_cons {Z : Finset (ℤ × ℤ)} {n : ℕ}
    (F : MarkedPhysicalPositionPath Z n → ℂ) (root : Z) (tail : Fin n → Z) :
    markedPhysicalPositionPathExtend F
      (Fin.cons (α := fun _ : Fin (n+1) => ℤ × ℤ) root.1 (fun v => (tail v).1)) =
      F (Fin.cons (α := fun _ : Fin (n+1) => Z) root tail) := by
  have h : ∀ v,(Fin.cons (α := fun _ : Fin (n+1) => ℤ × ℤ) root.1 (fun v => (tail v).1)) v∈Z := by
    intro v
    cases v using Fin.cases with
    | zero => exact root.2
    | succ k => exact (tail k).2
  rw [markedPhysicalPositionPathExtend,dite_eq_left h]
  apply congrArg F
  funext v
  apply Subtype.ext
  cases v using Fin.cases <;> rfl

def markedPhysicalPositionRootSum {Z : Finset (ℤ × ℤ)} {n : ℕ}
    (F : MarkedPhysicalPositionPath Z n → ℂ) (root : ℤ × ℤ) : ℂ :=
  ∑ tail : Fin n → Z,markedPhysicalPositionPathExtend F
    (Fin.cons (α := fun _ : Fin (n+1) => ℤ × ℤ) root (fun v => (tail v).1))

theorem markedPhysicalPositionRootSum_zero {Z : Finset (ℤ × ℤ)} {n : ℕ}
    (F : MarkedPhysicalPositionPath Z n → ℂ) (root : ℤ × ℤ) (hroot : root∉Z) :
    markedPhysicalPositionRootSum F root=0 := by
  apply Finset.sum_eq_zero
  intro tail _
  unfold markedPhysicalPositionPathExtend
  apply dite_eq_right
  intro h
  exact hroot (h 0)

theorem markedPhysicalPositionPath_sum_roots {Z : Finset (ℤ × ℤ)} {n : ℕ}
    (F : MarkedPhysicalPositionPath Z n → ℂ) :
    (∑ p,F p)=∑ root∈Z,markedPhysicalPositionRootSum F root := by
  have h := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Z)) F
  rw [Fintype.sum_prod_type] at h
  calc
    _ = ∑ root : Z,∑ tail : Fin n → Z,F (Fin.cons root tail) := h.symm
    _ = ∑ root : Z,markedPhysicalPositionRootSum F root.1 := by
      apply Finset.sum_congr rfl
      intro root _
      unfold markedPhysicalPositionRootSum
      simp_rw [markedPhysicalPositionPathExtend_cons]
    _ = _ := Finset.sum_coe_sort _ _

theorem markedPhysicalPositionRootSum_coordinates {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1<A) (hC : 1<C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) (n : ℕ) (F : MarkedPhysicalPositionPath Z n → ℂ) :
    markedPhysicalPositionRootSum F (markedPhysicalCanonicalRootPosition r) =
      ∑ tail : Fin n → ↥(markedPhysicalCanonicalTargets hA hC r Z),
        markedPhysicalPositionPathExtend F
          (Fin.cons (α := fun _ : Fin (n+1) => ℤ × ℤ) (markedPhysicalCanonicalRootPosition r)
            (fun v => markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
              (markedPhysicalCanonicalCompletion r) (tail v).1)) := by
  let e := markedPhysicalFiniteTargetEquiv hA hC r Z
  have h := Equiv.sum_comp (Equiv.piCongrRight (fun _ : Fin n => e))
    (fun tail => markedPhysicalPositionPathExtend F
      (Fin.cons (α := fun _ : Fin (n+1) => ℤ × ℤ) (markedPhysicalCanonicalRootPosition r)
        (fun v => (e.symm (tail v)).1)))
  simp only [Equiv.piCongrRight_apply,Pi.map_apply,Equiv.symm_apply_apply] at h
  simpa only [markedPhysicalPositionRootSum,e,markedPhysicalFiniteTargetEquiv_symm_apply] using h

theorem markedPhysicalPositionPath_sum_residue_coordinates
    {S : ℕ} [NeZero S] {A B C D : ℝ} (hA : 1<A) (hC : 1<C)
    (Z : Finset (ℤ × ℤ)) (hbox : Z⊆markedPhysicalPrimitiveBox A B C D)
    (n : ℕ) (F : MarkedPhysicalPositionPath Z n → ℂ) :
    (∑ p,F p)=
      ∑ r : MarkedPhysicalCanonicalRoot S A B C D,
        ∑ tail : Fin n → ↥(markedPhysicalCanonicalTargets hA hC r Z),
          markedPhysicalPositionPathExtend F
            (Fin.cons (α := fun _ : Fin (n+1) => ℤ × ℤ) (markedPhysicalCanonicalRootPosition r)
              (fun v => markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
                (markedPhysicalCanonicalCompletion r) (tail v).1)) := by
  calc
    _ = ∑ root∈Z,markedPhysicalPositionRootSum F root := markedPhysicalPositionPath_sum_roots F
    _ = ∑ root∈markedPhysicalPrimitiveBox A B C D,markedPhysicalPositionRootSum F root := by
      apply Finset.sum_subset hbox
      intro root _ hr
      exact markedPhysicalPositionRootSum_zero F root hr
    _ = ∑ r : MarkedPhysicalCanonicalRoot S A B C D,
        markedPhysicalPositionRootSum F (markedPhysicalCanonicalRootPosition r) := by
      have h := Equiv.sum_comp (markedPhysicalCanonicalRootEquiv (S := S) (B := B) (D := D) hA hC)
        (fun root => markedPhysicalPositionRootSum F root.1)
      have hpos (r : MarkedPhysicalCanonicalRoot S A B C D) :
          ((markedPhysicalCanonicalRootEquiv (S := S) (B := B) (D := D) hA hC) r).1=
            markedPhysicalCanonicalRootPosition r := rfl
      simp only [hpos] at h
      rw [Finset.sum_coe_sort] at h
      exact h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      exact markedPhysicalPositionRootSum_coordinates hA hC r Z n F

end
end ArtinMatthews
