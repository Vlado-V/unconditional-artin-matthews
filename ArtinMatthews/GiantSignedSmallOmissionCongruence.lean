module

public import ArtinMatthews.GiantSignedSmallOmissions
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

/-! Multiplication by the omitted product exposes the actual promotion
congruence. Its bounded positive integer representatives give a unique omission. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

section Congruence
variable {S : Type*} [Fintype S] {P : S → Finset ℕ} {M ell p : ℕ}
private theorem giantSignedSmallPromotion_cleared
    (a : MarkedPhysicalMarking P M) (r c : ZMod p)
    (U : GiantSignedSmallOmission S M ell)
    (h : r + c * (giantSignedSmallCopiedProduct a U : ZMod p) = 0) :
    r * (giantSignedSmallOmittedProduct a U : ZMod p) +
      c * (markedPhysicalMarkingProduct a : ZMod p) = 0 := by
  have hp := congrArg (fun z : ℕ => (z : ZMod p)) (giantSignedSmallCopied_mul_omitted a U)
  simp only [Nat.cast_mul] at hp
  calc
    _ = (r + c * (giantSignedSmallCopiedProduct a U : ZMod p)) *
        (giantSignedSmallOmittedProduct a U : ZMod p) := by rw [← hp]; ring
    _ = 0 := by rw [h, zero_mul]

variable [Fact p.Prime]

theorem giantSignedSmallPromotion_residue_ne_zero
    (a : MarkedPhysicalMarking P M) (r c : ZMod p) (hc : c ≠ 0)
    (hF : (markedPhysicalMarkingProduct a : ZMod p) ≠ 0)
    (U : GiantSignedSmallOmission S M ell)
    (h : r + c * (giantSignedSmallCopiedProduct a U : ZMod p) = 0) : r ≠ 0 := by
  intro hr
  have he := giantSignedSmallPromotion_cleared a r c U h
  rw [hr, zero_mul, zero_add] at he
  exact (mul_ne_zero hc hF) he

theorem giantSignedSmallPromotion_unique
    (hP : ∀ g q, q ∈ P g → q.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    (r c : ZMod p) (hc : c ≠ 0) (hF : (markedPhysicalMarkingProduct a : ZMod p) ≠ 0)
    (hbound : ∀ U : GiantSignedSmallOmission S M ell, giantSignedSmallOmittedProduct a U < p)
    (U V : GiantSignedSmallOmission S M ell)
    (hU : r + c * (giantSignedSmallCopiedProduct a U : ZMod p) = 0)
    (hV : r + c * (giantSignedSmallCopiedProduct a V : ZMod p) = 0) : U = V := by
  have hr := giantSignedSmallPromotion_residue_ne_zero a r c hc hF U hU
  have hU' := giantSignedSmallPromotion_cleared a r c U hU
  have hV' := giantSignedSmallPromotion_cleared a r c V hV
  have he : r * (giantSignedSmallOmittedProduct a U : ZMod p) =
      r * (giantSignedSmallOmittedProduct a V : ZMod p) := by
    linear_combination hU' - hV'
  have hprod := congrArg ZMod.val (mul_left_cancel₀ hr he)
  rw [ZMod.val_natCast_of_lt (hbound U), ZMod.val_natCast_of_lt (hbound V)] at hprod
  exact giantSignedSmallOmittedProduct_injective hP hdis a ha hprod

end Congruence
end
end ArtinMatthews
