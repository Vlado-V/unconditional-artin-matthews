module

public import ArtinMatthews.GiantSignedLifespanMemorySchedule
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

/-! Insert the ordered memory schedule into the original chronological
states, leaving both active arrays and endpoint permutations literal. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {A : ∀ g, PB g → Finset (Fin (n+1))}
    {c : ∀ g p, GiantSignedResidueLifespanChoice (A g p)}
    {offset : Fin (n+1) → ℤ} {q : Fin (n+1) → ℝ}

def giantSignedChronologyFromSchedule
    (data : GiantSignedLifespanScheduleData c offset q (fun i g => ell+(C i g).card))
    (small : Fin (n+1) → GiantTwoSidedResidueState PS (k+ell))
    (active : Fin (n+1) → MarkedPhysicalMarking PB (k+ell))
    (πS τS : Fin n → S → Equiv.Perm (Fin (k+ell)))
    (πB τB : Fin n → B → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary PB (C i)) :
    GiantSignedChronologicalChoices PS PB ell C data.batch where
  state v := (small v,active v,(data.memory v).1)
  deleted v := GiantSignedLifespanScheduleData.deleted v (data.memory v)
  born := data.born
  sourceSmallPermutation := πS
  targetSmallPermutation := τS
  sourceBigPermutation := πB
  targetBigPermutation := τB
  auxiliary := aux
  edge i := data.edge i (data.memory i.castSucc)

def giantSignedLifespanSmallState {M : ℕ} (labels : MarkedPhysicalMarking PS M)
    (root : GiantTwoSidedFullResidue PS) (d : ℤ)
    (hd : MarkedPhysicalMarkingDistinct labels)
    (hroot : ∀ j i, giantTwoSidedResidueTranslate (P := PS) d root (giantTwoSidedResidueIndex j (labels j i)) = 0) :
    GiantTwoSidedResidueState PS M :=
  ⟨(giantTwoSidedResidueTranslate (P := PS) d root,labels),⟨hd,hroot⟩⟩

end
end ArtinMatthews
