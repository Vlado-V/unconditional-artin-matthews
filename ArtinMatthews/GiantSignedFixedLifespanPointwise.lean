module

public import ArtinMatthews.GiantSignedChronologicalExteriorRoot
public import ArtinMatthews.GiantSignedFixedOrderedLifespan
public import ArtinMatthews.GiantSignedJoinedBigLifespan
public import ArtinMatthews.GiantSignedChronologicalSourceCoefficient
public import ArtinMatthews.GiantSignedFixedLifespanChronology
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

/-! On each fixed ordered term, the original chronological coefficient
has the original root scalar and the literal inverse birth factorials. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {κ : Fin n → ℤ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedFixedOrderedLifespan_weight_eq
    (q ρ θ : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hq : 0 ≤ q) (hn : 0 < n) (hV : ∀ g, bandReciprocalMass (PB g) ≠ 0) (hρ : ρ ≠ 0)
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeBaseline (markedMemoryVisitQ q n) p.val ≠ 0)
    (x : GiantSignedFixedOrderedLifespan PS PB ell C κ (markedMemoryVisitQ q n)) :
    let z := giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize x
    giantSignedChronologicalDistinctWeight (fun g => giantSignedTiltedPrimeLaw (PB g) (markedMemoryVisitQ q n))
      (fun g => bandReciprocalMass (PB g)) κ q (markedMemoryVisitQ q n) ρ θ ζ K z.2 =
      (giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ)^n *
        giantTwoSidedRootScalar (giantSignedChronologicalJoinedPattern C) x.1.labels
          x.1.sourcePermutation x.1.targetPermutation x.1.auxiliary ζ
          (fun i => giantSignedJoinedCoefficient (PS := PS) (K i)) *
        ((giantTwoSidedIndependentResidueFactor PS (giantSignedSmallMarking x.1.labels) q
          x.1.offset x.1.smallRoot / Fintype.card (GiantTwoSidedFullResidue PS) : ℝ) : ℂ) *
        fourier (x.1.offset (Fin.last n)) (θ : AddCircle (1 : ℝ)) *
        giantSignedChronologicalBirthFactor z.1 *
        (giantSignedJoinedBigLifespanNormalizedProduct x.1.labels x.1.offset (markedMemoryVisitQ q n) x.2.1.val : ℂ) := by
  let vq := markedMemoryVisitQ q n
  let ν (g : B) := giantSignedTiltedPrimeLaw (PB g) vq
  let V (g : B) := bandReciprocalMass (PB g)
  let path := x.1
  let c := x.2.1
  let order := x.2.2
  let d := path.schedule hP hdis hκ hsize c.property order
  let h := path.chronology d
  let z := giantSignedFixedOrderedLifespan_admissible hP hdis hκ hsize x
  have hl : giantSignedChronologicalJoinedLabels h = path.labels := path.chronology_labels d
  have ho : giantSignedChronologicalJoinedOffset h κ = path.offset := path.chronology_offset d
  let L := giantSignedChronologicalDistinctWeight ν V κ q vq ρ θ ζ K h
  let F := (giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ)^n *
    giantSignedChronologicalOriginalRootScalar h ζ K *
    ((giantTwoSidedIndependentResidueFactor PS (fun v => (h.state v).1.val.2) q
      (giantSignedChronologicalJoinedOffset h κ) (h.state 0).1.val.1 /
      Fintype.card (GiantTwoSidedFullResidue PS) : ℝ) : ℂ) *
    fourier (giantSignedChronologicalJoinedOffset h κ (Fin.last n)) (θ : AddCircle (1 : ℝ)) *
    giantSignedChronologicalBirthFactor d.batch
  let Compare (labels : Fin (n+1) → MarkedPhysicalMarking (Sum.elim PS PB) (k+ell)) (o : Fin (n+1) → ℤ) :=
    ∀ (a : {a : GiantSignedJoinedBigLifespanChoice labels // GiantSignedJoinedBigLifespanSupported labels o vq a}),
      GiantSignedChronologicalLifespanCoefficientData a.val h o →
      L = F * (giantSignedJoinedBigLifespanNormalizedProduct labels o vq a.val : ℂ)
  have hPS (g : S) (p : ℕ) (hp : p ∈ PS g) : p.Prime := hP (Sum.inl g) p hp
  have hdisS : Pairwise (fun g g' : S => Disjoint (PS g) (PS g')) :=
    fun _ _ hne => hdis (fun he => hne (Sum.inl.inj he))
  have hOrig : Compare (giantSignedChronologicalJoinedLabels h) (giantSignedChronologicalJoinedOffset h κ) :=
    fun a cert => giantSignedChronologicalDistinctWeight_eq_source_pointwise h κ ρ θ ζ K z.property.1
      z.property.2 a cert hPS hdisS hq hn hV hρ hb
  have hPath : Compare path.labels path.offset := ho ▸ hl ▸ hOrig
  have hCoef : GiantSignedChronologicalLifespanCoefficientData (A := path.visits) c.val h path.offset :=
    giantSignedLifespanPath_coefficientData path hP hdis hκ hsize c.property order
  have he := hPath c hCoef
  have hRoot : (h.state 0).1.val.1 = path.smallRoot := by
    change giantTwoSidedResidueTranslate (P := PS) (path.offset 0) path.smallRoot = path.smallRoot
    rw [GiantSignedLifespanOriginalPath.offset,giantTwoSidedPathOffset_zero]
    funext p
    simp only [giantTwoSidedResidueTranslate,Int.cast_zero,add_zero]
  have hMarks : (fun v => (h.state v).1.val.2) = giantSignedSmallMarking path.labels := rfl
  change L = _
  rw [he]
  dsimp only [F]
  rw [giantSignedChronologicalOriginalRootScalar,hl,path.chronology_sourcePermutation d,
    path.chronology_targetPermutation d,path.chronology_auxiliary d,hMarks,ho,hRoot]
  rfl

end
end ArtinMatthews
