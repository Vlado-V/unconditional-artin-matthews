module

public import ArtinMatthews.GiantSignedChronologicalStatic
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

/-! The small coordinates retain the original two half dampings and the
same integer offsets as the joined chronological path. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

theorem giantSignedChronologicalSmall_damping_factor
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun a b => Disjoint (PS a) (PS b)))
    {q : ℝ} (hq : 0 ≤ q) (hn : 0 < n)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    (hc : GiantSignedChronologicalCompatible κ h) :
    (∏ i : Fin n,
      giantTwoSidedResidueDamping PS (k+ell) q (giantSignedChronologicalSmallSource h i).val.1 *
        giantTwoSidedResidueDamping PS (k+ell) q (giantSignedChronologicalSmallTarget h i).val.1) =
      giantTwoSidedIndependentResidueFactor PS (fun v => (h.state v).1.val.2) q
        (giantSignedChronologicalJoinedOffset h κ) (h.state 0).1.val.1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  change (∏ i : Fin (m+1),
    giantTwoSidedResidueDamping PS (k+ell) q (h.state i.castSucc).1.val.1 *
      giantTwoSidedResidueDamping PS (k+ell) q (h.state i.succ).1.val.1) = _
  rw [giantTwoSidedResiduePath_damping_schedule hPS hdis hq (fun v => (h.state v).1)]
  unfold giantTwoSidedIndependentResidueFactor
  apply Finset.prod_congr rfl
  intro v _
  have ha : giantTwoSidedResidueActiveIndicator (h.state v).1.val.2
      (giantTwoSidedResidueTranslate (giantSignedChronologicalJoinedOffset h κ v)
        (h.state 0).1.val.1) = 1 := by
    rw [← giantSignedChronologicalSmallResidue_eq_translate h κ hc v,
      giantTwoSidedResidueActiveIndicator_eq, ite_eq_left (h.state v).1.property.2]
  rw [ha, one_mul, ← giantSignedChronologicalSmallResidue_eq_translate h κ hc v]

end
end ArtinMatthews
