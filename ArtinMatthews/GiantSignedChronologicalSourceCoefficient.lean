module

public import ArtinMatthews.GiantSignedChronologicalExteriorRoot
public import ArtinMatthews.GiantSignedJoinedBigLifespanSupport
public import ArtinMatthews.GiantPrimeRowSource
public import ArtinMatthews.GiantSignedChronologicalSmallFactor
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

/-! The fixed actual chronological row term equals the original joined
root coefficient, its actual small residue term, and its big lifespan term. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

theorem giantSignedChronologicalExterior_mul_bandNormalization_eq_source
    (κ : Fin n → ℤ) {q : ℝ} (θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hdis : Pairwise (fun a b => Disjoint (PS a) (PS b)))
    (hq : 0 ≤ q) (hn : 0 < n) (hc : GiantSignedChronologicalCompatible κ h) :
    giantSignedChronologicalExterior h κ q θ ζ K *
        giantSignedChronologicalBandNormalization (fun g => bandReciprocalMass (PB g)) C ell =
      ((giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ) ^ n) *
        giantSignedChronologicalOriginalRootScalar h ζ K *
        ((giantTwoSidedIndependentResidueFactor PS (fun v => (h.state v).1.val.2) q
          (giantSignedChronologicalJoinedOffset h κ) (h.state 0).1.val.1 /
            Fintype.card (GiantTwoSidedFullResidue PS) : ℝ) : ℂ) *
        fourier (giantSignedChronologicalJoinedOffset h κ (Fin.last n)) (θ : AddCircle (1 : ℝ)) := by
  have hd : (∏ i : Fin n,
      (giantTwoSidedResidueDamping PS (k+ell) q (giantSignedChronologicalSmallSource h i).val.1 : ℂ) *
        (giantTwoSidedResidueDamping PS (k+ell) q (giantSignedChronologicalSmallTarget h i).val.1 : ℂ)) =
      (giantTwoSidedIndependentResidueFactor PS (fun v => (h.state v).1.val.2) q
        (giantSignedChronologicalJoinedOffset h κ) (h.state 0).1.val.1 : ℂ) := by
    have hp := congrArg Complex.ofRealHom (giantSignedChronologicalSmall_damping_factor hPS hdis hq hn h κ hc)
    have hcoe (x : ℝ) : Complex.ofRealHom x = (x : ℂ) := rfl
    simp only [map_prod, map_mul] at hp
    simpa only [hcoe] using hp
  rw [giantSignedChronologicalExterior_mul_bandNormalization_eq_root h κ q θ ζ K, hd]
  simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  ac_rfl

theorem giantSignedChronologicalDistinctWeight_eq_source_pointwise
    (κ : Fin n → ℤ) {q : ℝ} (ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))
    (c : {c : GiantSignedJoinedBigLifespanChoice (giantSignedChronologicalJoinedLabels h) //
      GiantSignedJoinedBigLifespanSupported (giantSignedChronologicalJoinedLabels h)
        (giantSignedChronologicalJoinedOffset h κ) (markedMemoryVisitQ q n) c})
    (data : GiantSignedChronologicalLifespanCoefficientData c.val h (giantSignedChronologicalJoinedOffset h κ))
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hdis : Pairwise (fun a b => Disjoint (PS a) (PS b)))
    (hq : 0 ≤ q) (hn : 0 < n)
    (hV : ∀ g, bandReciprocalMass (PB g) ≠ 0) (hρ : ρ ≠ 0)
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeBaseline (markedMemoryVisitQ q n) p.val ≠ 0) :
    giantSignedChronologicalDistinctWeight
      (fun g p => giantSignedTiltedPrimeLaw (PB g) (markedMemoryVisitQ q n) p)
      (fun g => bandReciprocalMass (PB g)) κ q (markedMemoryVisitQ q n) ρ θ ζ K h =
      ((giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ) ^ n) *
        giantSignedChronologicalOriginalRootScalar h ζ K *
        ((giantTwoSidedIndependentResidueFactor PS (fun v => (h.state v).1.val.2) q
          (giantSignedChronologicalJoinedOffset h κ) (h.state 0).1.val.1 /
            Fintype.card (GiantTwoSidedFullResidue PS) : ℝ) : ℂ) *
        fourier (giantSignedChronologicalJoinedOffset h κ (Fin.last n)) (θ : AddCircle (1 : ℝ)) *
        giantSignedChronologicalBirthFactor batch *
        (giantSignedJoinedBigLifespanNormalizedProduct (giantSignedChronologicalJoinedLabels h)
          (giantSignedChronologicalJoinedOffset h κ) (markedMemoryVisitQ q n) c.val : ℂ) := by
  let o := giantSignedChronologicalJoinedOffset h κ
  let vq := markedMemoryVisitQ q n
  have hB (g : B) (p : PB g) : giantSignedPrimeBaseline vq p.val ≠ 0 :=
    hb (giantTwoSidedResidueIndex g p)
  have hproduct : (∏ g, ∏ p : PB g,
      ((giantSignedResidueLifespanWeight p.val o vq
        (giantSignedActualActiveVisits (giantSignedChronologicalJoinedLabels h) p.val) (c.val g p) /
          giantSignedPrimeBaseline vq p.val : ℝ) : ℂ)) =
      (giantSignedJoinedBigLifespanNormalizedProduct (giantSignedChronologicalJoinedLabels h) o vq c.val : ℂ) := by
    unfold giantSignedJoinedBigLifespanNormalizedProduct
    change _ = Complex.ofRealHom _
    simp only [map_prod, giantSignedRowBaseline_eq_source]
    rfl
  rw [giantSignedChronologicalDistinctWeight_eq_lifespan h c.val o κ q vq ρ θ ζ K ha hd data
    c.property hV hρ hB, hproduct]
  rw [show giantSignedChronologicalExterior h κ q θ ζ K * giantSignedChronologicalBirthFactor batch *
      giantSignedChronologicalBandNormalization (fun g => bandReciprocalMass (PB g)) C ell =
    (giantSignedChronologicalExterior h κ q θ ζ K *
      giantSignedChronologicalBandNormalization (fun g => bandReciprocalMass (PB g)) C ell) *
        giantSignedChronologicalBirthFactor batch by ac_rfl]
  rw [giantSignedChronologicalExterior_mul_bandNormalization_eq_source h κ θ ζ K hPS hdis hq hn ha.compatible]

end
end ArtinMatthews
