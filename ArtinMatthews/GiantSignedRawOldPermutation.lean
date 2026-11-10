module

public import ArtinMatthews.GiantSignedRawEdgeEnumeration
public import ArtinMatthews.GiantSignedEdgeEquivariance
public import ArtinMatthews.GiantSignedEdgeTargetSymmetry
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

/-! Old pending indices are relabelled through the actual injection. All
geometric labels, four slot permutations and store/target subsets stay fixed. -/
namespace ArtinMatthews
noncomputable section

def giantSignedEdgeOldChoiceEquiv {B : Type*} {t d : B → ℕ}
    (σ : ∀ g, Equiv.Perm (Fin (d g))) : GiantSignedEdgeChoice t d ≃ GiantSignedEdgeChoice t d :=
  Equiv.sigmaCongrRight fun _ => Equiv.sigmaCongrRight fun T =>
    Equiv.piCongrRight fun g => Equiv.embeddingCongr (Equiv.refl (Fin (T g).card)) (σ g)

theorem giantSignedEdgeOldChoiceEquiv_apply {B : Type*} {t d : B → ℕ}
    (σ : ∀ g, Equiv.Perm (Fin (d g))) (c : GiantSignedEdgeChoice t d) :
    giantSignedEdgeOldChoiceEquiv σ c =
      ⟨c.1, c.2.1, fun g => giantSignedMovedPromotion (σ g) (c.2.2 g)⟩ := rfl

variable {S B : Type*} [Fintype S] {PS : S → Finset ℕ} {PB : B → Finset ℕ}
    {k ell : ℕ} {C : B → Finset (Fin k)}

def giantSignedRawEdgeOldEquiv (m : GiantSignedMemory PB)
    (σ : ∀ g, Equiv.Perm (Fin (m.1 g))) :
    GiantSignedRawEdgeMove PS PB ell C (giantSignedMemoryPermute m σ) ≃
      GiantSignedRawEdgeMove PS PB ell C m :=
  (giantSignedRawEdgeMoveEquiv (giantSignedMemoryPermute m σ)).trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.prodCongr (giantSignedEdgeOldChoiceEquiv σ) (Equiv.refl _))))).trans
      (giantSignedRawEdgeMoveEquiv m).symm)

theorem giantSignedRawEdgeOldEquiv_choice (m : GiantSignedMemory PB)
    (σ : ∀ g, Equiv.Perm (Fin (m.1 g)))
    (r : GiantSignedRawEdgeMove PS PB ell C (giantSignedMemoryPermute m σ)) :
    (giantSignedRawEdgeOldEquiv m σ r).choice =
      ⟨r.choice.1, r.choice.2.1,
        fun g => giantSignedMovedPromotion (σ g) (r.choice.2.2 g)⟩ := rfl

section State
variable [Fintype B]

theorem giantSignedRawEdgeOldEquiv_product
    (s : GiantSignedState PS PB (k+ell)) (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
    (r : GiantSignedRawEdgeMove PS PB ell C (giantSignedMemoryPermute s.2.2 σ)) :
    giantSignedRawEdgeProduct (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
      giantSignedRawEdgeProduct s (giantSignedRawEdgeOldEquiv s.2.2 σ r) := rfl

theorem giantSignedRawEdgeOldEquiv_condition (κ : ℤ)
    (s : GiantSignedState PS PB (k+ell)) (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
    (r : GiantSignedRawEdgeMove PS PB ell C (giantSignedMemoryPermute s.2.2 σ)) :
    GiantSignedRawEdgeCondition κ (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r ↔
      GiantSignedRawEdgeCondition κ s (giantSignedRawEdgeOldEquiv s.2.2 σ r) := Iff.rfl

theorem giantSignedRawEdgeOldEquiv_target_test (κ : ℤ)
    (s : GiantSignedState PS PB (k+ell)) (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
    (r : GiantSignedRawEdgeMove PS PB ell C (giantSignedMemoryPermute s.2.2 σ))
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ z a, GiantSignedMemorySymmetric (fun m => f (z,a,m))) :
    f (giantSignedRawEdgeTarget κ (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r) =
      f (giantSignedRawEdgeTarget κ s (giantSignedRawEdgeOldEquiv s.2.2 σ r)) := by
  exact giantSignedEdgeTarget_symmetric_test
    (κ * (giantSignedRawEdgeProduct (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r : ℤ))
    s.2.2 (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource
      (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r)) r.choice σ
    (fun m => f ((giantTwoSidedResiduePermute r.targetSmallPermutation).symm r.smallTarget,
      (giantSignedGroupedTuplePermutation r.targetBigPermutation).symm r.bigTarget, m))
    (hf _ _)

end State
end
end ArtinMatthews
