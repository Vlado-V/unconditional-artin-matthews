module

public import ArtinMatthews.GiantSmallBigResidueSplit
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

/-! The numeric big-prime union and the actual grouped lifespans carry
exactly the same choices and normalized weights. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] {PS : S → Finset ℕ} {PB : B → Finset ℕ}

/-- The original residue index is bijective on the disjoint big bands. -/
def giantSignedBigBandPrimeEquiv (PB : B → Finset ℕ)
    (hB : Pairwise (fun g h => Disjoint (PB g) (PB h))) :
    (Σ g, ↥(PB g)) ≃ ↥(markedPhysicalBandPrimes PB) :=
  Equiv.ofBijective (fun a => giantTwoSidedResidueIndex a.1 a.2) ⟨by
    rintro ⟨g,p⟩ ⟨h,q⟩ he
    have hp : p.val = q.val := congrArg Subtype.val he
    have hg : g = h := by
      by_contra hn
      exact Finset.disjoint_left.mp (hB hn) p.property (hp.symm ▸ q.property)
    subst h
    have heq : p = q := Subtype.ext hp
    subst q
    rfl, by
    intro p
    obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp p.property
    exact ⟨⟨g, ⟨p.val, hg⟩⟩, Subtype.ext rfl⟩⟩

@[simp] theorem giantSignedBigBandPrimeEquiv_apply
    (hB : Pairwise (fun g h => Disjoint (PB g) (PB h))) (g : B) (p : PB g) :
    giantSignedBigBandPrimeEquiv PB hB ⟨g, p⟩ = giantTwoSidedResidueIndex g p := rfl

private theorem joined_big_bands_disjoint
    (hdis : Pairwise (fun g h : Sum S B => Disjoint (Sum.elim PS PB g) (Sum.elim PS PB h))) :
    Pairwise (fun g h => Disjoint (PB g) (PB h)) := by
  intro g h hne
  exact hdis (fun he : (Sum.inr g : Sum S B) = Sum.inr h => hne (Sum.inr.inj he))

variable {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking (Sum.elim PS PB) M)
    (hdis : Pairwise (fun g h : Sum S B => Disjoint (Sum.elim PS PB g) (Sum.elim PS PB h)))

abbrev GiantSignedJoinedBigLifespanChoice :=
  (g : B) → (p : PB g) → GiantSignedResidueLifespanChoice (giantSignedActualActiveVisits labels p.val)

def giantSignedJoinedBigLifespanEquiv :
    GiantSignedFullPrimeLifespanChoice (giantSignedBigMarking labels) ≃
      GiantSignedJoinedBigLifespanChoice labels :=
  let e := giantSignedBigBandPrimeEquiv PB (joined_big_bands_disjoint hdis)
  let fibers (p : ↥(markedPhysicalBandPrimes PB)) :=
    GiantSignedResidueLifespanChoice (giantSignedActualActiveVisits (giantSignedBigMarking labels) p.val)
  (Equiv.piCongrLeft' fibers e.symm).trans <|
    (Equiv.piCongrRight (fun a => Equiv.cast (congrArg GiantSignedResidueLifespanChoice
      (giantSignedBigActiveVisits labels (giantSignedSmallBigPrimes_disjoint hdis) (e a).property).symm))).trans
      (Equiv.piCurry (fun g (p : PB g) => GiantSignedResidueLifespanChoice (giantSignedActualActiveVisits labels p.val)))

private theorem weight_cast {p : ℕ} (offset : Fin (n+1) → ℤ) (q : Fin (n+1) → ℝ)
    {A A' : Finset (Fin (n+1))} (he : A = A') (c : GiantSignedResidueLifespanChoice A) :
    giantSignedResidueLifespanWeight p offset q A' (Equiv.cast (congrArg GiantSignedResidueLifespanChoice he) c) =
      giantSignedResidueLifespanWeight p offset q A c := by
  subst A'
  rfl

theorem giantSignedJoinedBigLifespanEquiv_weight (offset : Fin (n+1) → ℤ) (q : Fin (n+1) → ℝ)
    (c : GiantSignedFullPrimeLifespanChoice (giantSignedBigMarking labels)) (g : B) (p : PB g) :
    giantSignedResidueLifespanWeight p.val offset q (giantSignedActualActiveVisits labels p.val)
      (giantSignedJoinedBigLifespanEquiv labels hdis c g p) =
    giantSignedResidueLifespanWeight p.val offset q
      (giantSignedActualActiveVisits (giantSignedBigMarking labels) p.val) (c (giantTwoSidedResidueIndex g p)) :=
  weight_cast offset q (giantSignedBigActiveVisits labels (giantSignedSmallBigPrimes_disjoint hdis)
    (giantTwoSidedResidueIndex g p).property).symm (c (giantTwoSidedResidueIndex g p))

def giantSignedJoinedBigLifespanNormalizedProduct (offset : Fin (n+1) → ℤ) (q : Fin (n+1) → ℝ)
    (c : GiantSignedJoinedBigLifespanChoice labels) : ℝ :=
  ∏ g, ∏ p : PB g,
    giantSignedResidueLifespanWeight p.val offset q (giantSignedActualActiveVisits labels p.val) (c g p) /
      giantSignedPrimeResidueBaseline p.val q

theorem giantSignedJoinedBigLifespanEquiv_normalizedProduct (offset : Fin (n+1) → ℤ) (q : Fin (n+1) → ℝ)
    (c : GiantSignedFullPrimeLifespanChoice (giantSignedBigMarking labels)) :
    giantSignedJoinedBigLifespanNormalizedProduct labels offset q (giantSignedJoinedBigLifespanEquiv labels hdis c) =
      ∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedResidueLifespanWeight p.val offset q
        (giantSignedActualActiveVisits (giantSignedBigMarking labels) p.val) (c p) /
          giantSignedPrimeResidueBaseline p.val q := by
  let f (p : ↥(markedPhysicalBandPrimes PB)) := giantSignedResidueLifespanWeight p.val offset q
    (giantSignedActualActiveVisits (giantSignedBigMarking labels) p.val) (c p) /
      giantSignedPrimeResidueBaseline p.val q
  let e := giantSignedBigBandPrimeEquiv PB (joined_big_bands_disjoint hdis)
  unfold giantSignedJoinedBigLifespanNormalizedProduct
  calc
    _ = ∏ g, ∏ p : PB g, f (giantTwoSidedResidueIndex g p) := by
      apply Finset.prod_congr rfl
      intro g _
      apply Finset.prod_congr rfl
      intro p _
      dsimp only [f]
      rw [giantSignedJoinedBigLifespanEquiv_weight labels hdis]
      rfl
    _ = ∏ g, ∏ p : PB g, f (e ⟨g, p⟩) := by
      simp only [e, giantSignedBigBandPrimeEquiv_apply]
    _ = ∏ a : Σ g, ↥(PB g), f (e a) := (Fintype.prod_sigma (fun a : Σ g, ↥(PB g) => f (e a))).symm
    _ = _ := e.prod_comp f

theorem giantSignedBigBaseline_product_eq_bands
    (hB : Pairwise (fun g h => Disjoint (PB g) (PB h))) (q : Fin (n+1) → ℝ) :
    (∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeResidueBaseline p.val q) =
      ∏ g, ∏ p : PB g, giantSignedPrimeResidueBaseline p.val q := by
  rw [← (giantSignedBigBandPrimeEquiv PB hB).prod_comp (fun p => giantSignedPrimeResidueBaseline p.val q),
    Fintype.prod_sigma]
  rfl

end
end ArtinMatthews
