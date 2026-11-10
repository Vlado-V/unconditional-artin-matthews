module

public import ArtinMatthews.GiantSignedChronologicalFrameBound
public import ArtinMatthews.GiantSignedChronologicalSupport
public import ArtinMatthews.GiantSignedChronologicalLineage
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

/-! Exact support of the distinct-birth chronology. Its active lists
are distinct and every realized memory lies in the finite band bound. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

theorem giantSignedChronologicalMarking_distinct (κ : Fin n → ℤ)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h)) (i : Fin (n+1)) :
    MarkedPhysicalMarkingDistinct (h.state i).2.1 := by
  intro g u v huv
  have hLive := giantSignedBirthLineage_injective
    (giantSignedChronologicalPreLineage h κ ha i g) hd
  exact Sum.inl.inj (hLive (show giantSignedStateLivePrime (h.state i) g (.inl u) =
    giantSignedStateLivePrime (h.state i) g (.inl v) from huv))

theorem giantSignedChronologicalMemoryCap_of_distinct (κ : Fin n → ℤ)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h)) :
    GiantSignedChronologicalMemoryCap (∑ g, (PB g).card) h := by
  constructor <;> intro i <;> apply Finset.sum_le_sum <;> intro g _
  · exact (Nat.le_add_left _ _).trans (giantSignedChronological_distinct_degrees h κ ha hd i g).1
  · exact (Nat.le_add_left _ _).trans (giantSignedChronological_distinct_degrees h κ ha hd i g).2.1

theorem giantSignedChronologicalDistinctWeight_support_cap (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : Fin n → ℤ) (q : ℝ) (visitQ : Fin (n+1) → ℝ) (ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hw : giantSignedChronologicalDistinctWeight ν V κ q visitQ ρ θ ζ K h ≠ 0) :
    GiantSignedChronologicalMemoryCap (∑ g, (PB g).card) h := by
  classical
  have hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h) := by
    by_contra hbad
    exact hw (ite_eq_right hbad)
  rw [giantSignedChronologicalDistinctWeight, ite_eq_left hd] at hw
  exact giantSignedChronologicalMemoryCap_of_distinct h κ
    (giantSignedChronologicalWeight_admissible ν V κ q visitQ ρ θ ζ K h hw) hd

end
end ArtinMatthews
