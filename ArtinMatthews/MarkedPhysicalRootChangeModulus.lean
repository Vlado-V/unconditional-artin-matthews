module

public import ArtinMatthews.MarkedPhysicalRootTargetReindex
public import ArtinMatthews.FixedURootReciprocalBoxes
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

/-! Changing the residue modulus does not change the canonical integer
completion or any relative coordinate. The proof uses the actual
determinant-one equation and the half-open choice of its first entry. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCanonicalCompletion_eq_of_position_eq
    {S T : ℕ} [NeZero S] [NeZero T] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D)
    (r' : MarkedPhysicalCanonicalRoot T A B C D)
    (he : markedPhysicalCanonicalRootPosition r=markedPhysicalCanonicalRootPosition r') :
    markedPhysicalCanonicalCompletion r=markedPhysicalCanonicalCompletion r' := by
  rcases r with ⟨g,⟨⟨u,c,v⟩,hp⟩⟩
  rcases r' with ⟨g',⟨⟨u',c',v'⟩,hp'⟩⟩
  have hu : u=u' := congrArg Prod.fst he
  have hv : v=v' := congrArg Prod.snd he
  subst u'
  subst v'
  obtain ⟨d,_,_,hc,hcu,_,_,hd,_⟩ :=
    fixedURootReciprocal_box_canonical hA hC (by norm_num) (by norm_num) hp
  obtain ⟨d',_,_,hc',hcu',_,_,hd',_⟩ :=
    fixedURootReciprocal_box_canonical hA hC (by norm_num) (by norm_num) hp'
  have hcc := fixedURoot_canonical_entry_unique hc.le hcu hc'.le hcu' hd hd'
  subst c'
  rfl

def markedPhysicalCanonicalRootChangeModulus
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C) :
    MarkedPhysicalCanonicalRoot S A B C D ≃ MarkedPhysicalCanonicalRoot T A B C D :=
  (markedPhysicalCanonicalRootEquiv (S := S) (B := B) (D := D) hA hC).trans
    (markedPhysicalCanonicalRootEquiv (S := T) (B := B) (D := D) hA hC).symm

theorem markedPhysicalCanonicalRootChangeModulus_position
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) :
    markedPhysicalCanonicalRootPosition (markedPhysicalCanonicalRootChangeModulus S T hA hC r)=
      markedPhysicalCanonicalRootPosition r := by
  exact congrArg Subtype.val ((markedPhysicalCanonicalRootEquiv (S := T) (B := B) (D := D) hA hC).apply_symm_apply
    ((markedPhysicalCanonicalRootEquiv (S := S) (B := B) (D := D) hA hC) r))

theorem markedPhysicalCanonicalRootChangeModulus_completion
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) :
    markedPhysicalCanonicalCompletion (markedPhysicalCanonicalRootChangeModulus S T hA hC r)=
      markedPhysicalCanonicalCompletion r :=
  markedPhysicalCanonicalCompletion_eq_of_position_eq hA hC _ _
    (markedPhysicalCanonicalRootChangeModulus_position S T hA hC r)

theorem markedPhysicalCanonicalRootChangeModulus_lift
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) (z : ℤ × ℤ) :
    markedPhysicalRootLift
      (markedPhysicalCanonicalRootPosition (markedPhysicalCanonicalRootChangeModulus S T hA hC r))
      (markedPhysicalCanonicalCompletion (markedPhysicalCanonicalRootChangeModulus S T hA hC r)) z=
      markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r) z := by
  rw [markedPhysicalCanonicalRootChangeModulus_position,markedPhysicalCanonicalRootChangeModulus_completion]

theorem markedPhysicalCanonicalRoot_sum_changeModulus
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (F : (ℤ × ℤ) → (ℤ × ℤ) → ℂ) :
    (∑ r : MarkedPhysicalCanonicalRoot S A B C D,
      F (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r))=
    ∑ r : MarkedPhysicalCanonicalRoot T A B C D,
      F (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r) := by
  calc
    _ = ∑ r : MarkedPhysicalCanonicalRoot S A B C D,
        F (markedPhysicalCanonicalRootPosition (markedPhysicalCanonicalRootChangeModulus S T hA hC r))
          (markedPhysicalCanonicalCompletion (markedPhysicalCanonicalRootChangeModulus S T hA hC r)) := by
      simp only [markedPhysicalCanonicalRootChangeModulus_position,markedPhysicalCanonicalRootChangeModulus_completion]
    _ = _ := Equiv.sum_comp (markedPhysicalCanonicalRootChangeModulus S T hA hC)
      (fun r : MarkedPhysicalCanonicalRoot T A B C D =>
        F (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r))

end
end ArtinMatthews
