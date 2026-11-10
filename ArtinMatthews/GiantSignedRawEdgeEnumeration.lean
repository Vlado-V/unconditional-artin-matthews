module

public import ArtinMatthews.GiantSignedRawEdgeData
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

/-! Exact finite enumeration of every raw edge move. All four endpoint
permutations, auxiliary labels, old-index choices and targets occur once. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {S B : Type*} [Fintype S] {PS : S → Finset ℕ} {PB : B → Finset ℕ}
    {k ell : ℕ} {C : B → Finset (Fin k)}

abbrev GiantSignedRawEdgeCoordinates (PS : S → Finset ℕ) (PB : B → Finset ℕ)
    {k : ℕ} (ell : ℕ) (C : B → Finset (Fin k)) (m : GiantSignedMemory PB) :=
  ((S → Equiv.Perm (Fin (k+ell))) × (B → Equiv.Perm (Fin (k+ell)))) ×
    ((S → Equiv.Perm (Fin (k+ell))) × (B → Equiv.Perm (Fin (k+ell)))) ×
    GiantTwoSidedPatternAuxiliary PB C ×
    GiantSignedEdgeChoice (fun g => ell + (C g).card) m.1 ×
    GiantTwoSidedResidueState PS (k+ell) × MarkedPhysicalMarking PB (k+ell)

def giantSignedRawEdgeMoveEquiv (m : GiantSignedMemory PB) :
    GiantSignedRawEdgeMove PS PB ell C m ≃ GiantSignedRawEdgeCoordinates PS PB ell C m where
  toFun r := ((r.sourceSmallPermutation, r.sourceBigPermutation),
    (r.targetSmallPermutation, r.targetBigPermutation), r.auxiliary, r.choice,
    r.smallTarget, r.bigTarget)
  invFun r :=
    { sourceSmallPermutation := r.1.1
      sourceBigPermutation := r.1.2
      targetSmallPermutation := r.2.1.1
      targetBigPermutation := r.2.1.2
      auxiliary := r.2.2.1
      choice := r.2.2.2.1
      smallTarget := r.2.2.2.2.1
      bigTarget := r.2.2.2.2.2 }
  left_inv r := by cases r; rfl
  right_inv r := by rcases r with ⟨⟨a,b⟩,⟨c,d⟩,e,f,g,h⟩; rfl

variable [Fintype B] [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedRawEdgeMove_sum (m : GiantSignedMemory PB)
    (F : GiantSignedRawEdgeMove PS PB ell C m → ℂ) :
    (∑ r : GiantSignedRawEdgeMove PS PB ell C m, F r) =
      ∑ πS : S → Equiv.Perm (Fin (k+ell)),
      ∑ πB : B → Equiv.Perm (Fin (k+ell)),
      ∑ τS : S → Equiv.Perm (Fin (k+ell)),
      ∑ τB : B → Equiv.Perm (Fin (k+ell)),
      ∑ aux : GiantTwoSidedPatternAuxiliary PB C,
      ∑ c : GiantSignedEdgeChoice (fun g => ell + (C g).card) m.1,
      ∑ tS : GiantTwoSidedResidueState PS (k+ell),
      ∑ tB : MarkedPhysicalMarking PB (k+ell),
        F ⟨πS,πB,τS,τB,aux,c,tS,tB⟩ := by
  have h := (giantSignedRawEdgeMoveEquiv (PS := PS) (C := C) m).symm.sum_comp F
  simpa only [Fintype.sum_prod_type, giantSignedRawEdgeMoveEquiv, Equiv.symm_mk,
    Equiv.coe_fn_mk] using h.symm

end
end ArtinMatthews
