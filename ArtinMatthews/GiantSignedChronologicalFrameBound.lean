module

public import ArtinMatthews.GiantSignedChronologicalChoices
public import ArtinMatthews.GiantSignedUniformBirthFrame
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

/-! A support condition on actual memories supplies the potential-frame
bound. The chronological state carrier itself retains every degree. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def GiantSignedChronologicalMemoryCap (H : ℕ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) : Prop :=
  (∀ i, (∑ g : B, (h.state i).2.2.1 g) ≤ H) ∧
    (∀ i, (∑ g : B, (giantSignedChronologicalGhostTarget h i).1 g) ≤ H)

omit [Fintype B] in
theorem giantSignedChronological_batch_le_degree
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (i : Fin (n+1)) (g : B) :
    batch i g ≤ (giantSignedChronologicalGhostTarget h i).1 g := by
  change batch i g ≤
    (giantSignedFixedGhostTarget (h.state i).2.2 (batch i) (h.deleted i) (h.born i)).1 g
  rw [giantSignedFixedGhostTarget_degree]
  omega

theorem giantSignedChronologicalMemoryCap_batches (H : ℕ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hcap : GiantSignedChronologicalMemoryCap H h) : ∀ i g, batch i g ≤ H := by
  intro i g
  have hs : (giantSignedChronologicalGhostTarget h i).1 g ≤
      ∑ j : B, (giantSignedChronologicalGhostTarget h i).1 j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  exact (giantSignedChronological_batch_le_degree h i g).trans (hs.trans (hcap.2 i))

theorem giantSignedChronologicalMemoryCap_birthGuard (H : ℕ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hcap : GiantSignedChronologicalMemoryCap H h) :
    GiantSignedBirthDistinct (giantSignedChronologicalBirthData h) ↔
      MarkedPerformedInjective (giantSignedUniformBirthValue
        (giantSignedChronologicalBirthData h) H
        (giantSignedChronologicalMemoryCap_batches H h hcap)) :=
  giantSignedBirthDistinct_iff_uniform _ _ _

end
end ArtinMatthews
