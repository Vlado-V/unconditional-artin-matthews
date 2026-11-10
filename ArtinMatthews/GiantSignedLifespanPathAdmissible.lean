module

public import ArtinMatthews.GiantSignedLifespanOriginalPath
public import ArtinMatthews.GiantSignedChronologicalSupport
public import ArtinMatthews.GiantTwoSidedResiduePathArithmetic
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

/-! The original fixed-path schedule satisfies every raw chronological
condition, including both literal free-slot divisibility bans. -/

namespace ArtinMatthews.GiantSignedLifespanOriginalPath
open Finset
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {κ : Fin n → ℤ}

theorem chronology_admissible
    (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ)
    {q : Fin (n+1) → ℝ} {c : ∀ (g : B) (p : PB g), GiantSignedResidueLifespanChoice (path.visits g p)}
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val path.offset q (path.visits g p) (c g p) ≠ 0)
    (order : ∀ v g, Fin (giantSignedGhostVisitBorn (c g) v).card ≃ ↥(giantSignedGhostVisitBorn (c g) v)) :
    let data := path.schedule hP hdis hκ hsize hw order
    GiantSignedChronologicalAdmissible κ (path.chronology data) := by
  let data := path.schedule hP hdis hκ hsize hw order
  let h := path.chronology data
  have hΔ (i : Fin n) : κ i * (giantSignedChronologicalProduct h i : ℤ) = data.increment i :=
    path.chronology_increment data i
  have hfree (i : Fin n) (g : B) (j : Fin (ell+(C i g).card)) :
      (¬ (data.source i g j).val ∣ giantSignedChronologicalProduct h i) ∧
        (¬ (data.target i g j).val ∣ giantSignedChronologicalProduct h i) := by
    rw [path.chronology_product data]
    exact giantTwoSidedIndependentPath_free_not_dvd hP hdis path.static i (Sum.inr g : S ⊕ B)
      (giantSignedPatternFreeSlotEquiv (C i g) ell j)
  change GiantSignedChronologicalAdmissible κ h
  refine ⟨?_,⟨data.memory_zero,data.after_last⟩,data.deleted_subset_zeros,?_⟩
  · intro i
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro g j
      exact (path.static.2 i).copied (Sum.inl g : S ⊕ B) j (notMem_empty j)
    · change giantTwoSidedResidueTranslate (P := PS) (path.offset i.succ) path.smallRoot =
        giantTwoSidedResidueTranslate (κ i * (giantSignedChronologicalProduct h i : ℤ))
          (giantTwoSidedResidueTranslate (P := PS) (path.offset i.castSucc) path.smallRoot)
      rw [hΔ, ← giantTwoSidedResidueTranslate_add, data.offset_step i]
    · intro g j hj
      exact (path.static.2 i).copied (Sum.inr g : S ⊕ B) j hj
    · have hm := congrArg Sigma.fst (data.memory_succ i)
      change (h.state i.succ).2.2 = giantSignedEdgeTarget
        (κ i * (giantSignedChronologicalProduct h i : ℤ))
        (giantSignedChronologicalGhostTarget h i.castSucc) (data.source i) (h.edge i)
      rw [hΔ]
      exact hm
    · intro g j
      exact (hfree i g (((h.edge i).1 g).orderEmbOfFin rfl j)).1
    · intro g a
      exact ⟨fun j l => (path.static.2 i).banned (Sum.inr g : S ⊕ B) (Sum.inl j) a l,
        fun j l => (path.static.2 i).banned (Sum.inr g : S ⊕ B) (Sum.inr j) a l⟩
  · intro i
    constructor
    · rw [hΔ]
      exact data.edge_hits i
    · intro g j
      exact (hfree i g (((h.edge i).2.1 g).orderEmbOfFin rfl j)).2

end
end ArtinMatthews.GiantSignedLifespanOriginalPath
