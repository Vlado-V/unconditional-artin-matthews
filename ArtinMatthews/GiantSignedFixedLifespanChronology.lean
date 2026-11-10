module

public import ArtinMatthews.GiantSignedFixedOrderedLifespan
public import ArtinMatthews.GiantSignedChronologicalReconstruction
public import ArtinMatthews.GiantSignedLifespanPathAdmissible
public import ArtinMatthews.GiantSignedLifespanPathCertificates
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
public import Mathlib.Tactic.ENatToNat
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

/-! The fixed-path chronology map preserves the actual choices and
birth orders. Its inverse reads the lifespans from their original indices. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {κ : Fin n → ℤ} {q : Fin (n+1) → ℝ}

private theorem fixedPath_ext {p p' : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ}
    (hl : p.labels = p'.labels) (hπ : p.sourcePermutation = p'.sourcePermutation)
    (hτ : p.targetPermutation = p'.targetPermutation) (ha : p.auxiliary = p'.auxiliary)
    (hr : p.smallRoot = p'.smallRoot) : p = p' := by
  cases p
  cases p'
  cases hl
  cases hπ
  cases hτ
  cases ha
  cases hr
  rfl

theorem giantSignedFixedOrderedLifespan_chronology_path
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    {x y : GiantSignedFixedOrderedLifespan PS PB ell C κ q}
    (he : giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize x =
      giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize y) : x.1 = y.1 := by
  let pack := giantSignedFixedOrderedLifespan_chronology (C := C) (ell := ell) hP hdis hκ hsize (q := q)
  let dx := x.1.schedule hP hdis hκ hsize x.2.1.property x.2.2
  let dy := y.1.schedule hP hdis hκ hsize y.2.1.property y.2.2
  have initial (a : GiantSignedFixedOrderedLifespan PS PB ell C κ q) : ((pack a).2.state 0).1.val.1 = a.1.smallRoot := by
    change giantTwoSidedResidueTranslate (P := PS) (a.1.offset 0) a.1.smallRoot = a.1.smallRoot
    rw [GiantSignedLifespanOriginalPath.offset,giantTwoSidedPathOffset_zero]
    funext p
    simp only [giantTwoSidedResidueTranslate,Int.cast_zero,add_zero]
  apply fixedPath_ext
  · exact (x.1.chronology_labels dx).symm.trans
      ((congrArg (fun z : GiantSignedFixedPackedChronology PS PB ell C => giantSignedChronologicalJoinedLabels z.2) he).trans
        (y.1.chronology_labels dy))
  · exact (x.1.chronology_sourcePermutation dx).symm.trans
      ((congrArg (fun z : GiantSignedFixedPackedChronology PS PB ell C => giantSignedChronologicalJoinedSourcePermutation z.2) he).trans
        (y.1.chronology_sourcePermutation dy))
  · exact (x.1.chronology_targetPermutation dx).symm.trans
      ((congrArg (fun z : GiantSignedFixedPackedChronology PS PB ell C => giantSignedChronologicalJoinedTargetPermutation z.2) he).trans
        (y.1.chronology_targetPermutation dy))
  · exact (x.1.chronology_auxiliary dx).symm.trans
      ((congrArg (fun z : GiantSignedFixedPackedChronology PS PB ell C => giantSignedChronologicalJoinedAuxiliary z.2) he).trans
        (y.1.chronology_auxiliary dy))
  · exact (initial x).symm.trans
      ((congrArg (fun z : GiantSignedFixedPackedChronology PS PB ell C => (z.2.state 0).1.val.1) he).trans (initial y))

def giantSignedFixedOrderedLifespan_admissible
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (x : GiantSignedFixedOrderedLifespan PS PB ell C κ q) :
    GiantSignedFixedAdmissibleChronology PS PB ell C κ := by
  let d := x.1.schedule hP hdis hκ hsize x.2.1.property x.2.2
  let h := x.1.chronology d
  have ha : GiantSignedChronologicalAdmissible κ h :=
    x.1.chronology_admissible hP hdis hκ hsize x.2.1.property x.2.2
  have hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h) :=
    giantSignedLifespanPath_birthDistinct x.1 hP hdis hκ hsize x.2.1.property x.2.2
  exact ⟨⟨d.batch,h⟩,ha,hd⟩

theorem giantSignedFixedOrderedLifespan_admissible_surjective
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hb : ∀ g (p : PB g), giantSignedPrimeResidueBaseline p.val q ≠ 0) :
    Function.Surjective (giantSignedFixedOrderedLifespan_admissible (C := C) (ell := ell) hP hdis hκ hsize (q := q)) := by
  rintro ⟨⟨batch,h⟩,ha,hd⟩
  have hSB (s : S) (b : B) : Disjoint (PS s) (PB b) :=
    hdis (show (Sum.inl s : S ⊕ B) ≠ Sum.inr b from by simp)
  let d := giantSignedChronologicalDecodeLifespans h κ q ha hd hP hdis hκ hsize hq0 hq1 hb
  let p := giantSignedChronologicalOriginalPath h κ ha hd hSB
  let order := giantSignedChronologicalRecoveredBirthOrders h κ q d
  refine ⟨⟨p,⟨d.choice,d.supported⟩,order⟩,Subtype.ext ?_⟩
  exact giantSignedChronologicalReconstruction h κ q ha hd hSB hP hdis hκ hsize d

end
end ArtinMatthews
