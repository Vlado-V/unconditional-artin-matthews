module

public import ArtinMatthews.GiantSignedChronologicalLifespanWeight
public import ArtinMatthews.GiantSignedChronologicalStatic
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantSignedCleanDisintegration
public import ArtinMatthews.GiantSignedSourceReturnScalars
public import ArtinMatthews.GiantTwoSidedResidueInitialMass
public import ArtinMatthews.GiantTwoSidedReturnFourier
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

/-! The original joined root scalar is the literal chronological exterior
with the original initial and free big-band volumes restored. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

private theorem ofReal_product {I : Type*} [Fintype I] (f : I → ℝ) :
    ((∏ i, f i : ℝ) : ℂ) = ∏ i, (f i : ℂ) :=
  map_prod Complex.ofRealHom f Finset.univ

private theorem joined_marked_mass (M : ℕ) :
    markedPhysicalMass (fun g => bandReciprocalMass (Sum.elim PS PB g)) M =
      markedPhysicalMass (fun g => bandReciprocalMass (PS g)) M *
        markedPhysicalMass (fun g => bandReciprocalMass (PB g)) M := by
  simp only [markedPhysicalMass, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

private theorem joined_fresh_mass (i : Fin n) :
    (giantTwoSidedPatternFreshMass (Sum.elim PS PB) (giantSignedChronologicalJoinedPattern C i) ell : ℂ) =
      (∏ g : S, ((bandReciprocalMass (PS g))⁻¹ : ℂ)^ell) *
        (giantTwoSidedPatternFreshMass PB (C i) ell : ℂ) := by
  have hr : giantTwoSidedPatternFreshMass (Sum.elim PS PB) (giantSignedChronologicalJoinedPattern C i) ell =
      (∏ g : S, (bandReciprocalMass (PS g))⁻¹ ^ ell) * giantTwoSidedPatternFreshMass PB (C i) ell := by
    simp only [giantTwoSidedPatternFreshMass, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      giantSignedChronologicalJoinedPattern, Finset.card_empty, add_zero]
  rw [hr, Complex.ofReal_mul, ofReal_product]
  simp only [Complex.ofReal_pow, Complex.ofReal_inv]

/-- The exact original coefficient on the joined marking array of the chronology. -/
def giantSignedChronologicalOriginalRootScalar (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) : ℂ :=
  giantTwoSidedRootScalar (giantSignedChronologicalJoinedPattern C)
    (giantSignedChronologicalJoinedLabels h) (giantSignedChronologicalJoinedSourcePermutation h)
    (giantSignedChronologicalJoinedTargetPermutation h) (giantSignedChronologicalJoinedAuxiliary h)
    ζ (fun i => giantSignedJoinedCoefficient (PS := PS) (K i))

theorem giantSignedChronologicalReturnPhase_eq (κ : Fin n → ℤ) (θ : ℝ) :
    (∏ i, idealAdditivePhase (θ * (κ i : ℝ)) (giantSignedChronologicalProduct h i)) =
      fourier (giantSignedChronologicalJoinedOffset h κ (Fin.last n)) (θ : AddCircle (1 : ℝ)) := by
  unfold giantSignedChronologicalJoinedOffset
  rw [giantTwoSidedFourier_path_product]
  simp_rw [giantSignedChronologicalJoinedIncrement_eq, giantSignedReturnPhase_eq_fourier]

theorem giantSignedChronologicalExterior_mul_bandNormalization_eq_root
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    (κ : Fin n → ℤ) (q θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) :
    giantSignedChronologicalExterior h κ q θ ζ K *
        giantSignedChronologicalBandNormalization (fun g => bandReciprocalMass (PB g)) C ell =
      ((giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ) ^ n) *
        giantSignedChronologicalOriginalRootScalar h ζ K *
        (Fintype.card (GiantTwoSidedFullResidue PS) : ℂ)⁻¹ *
        fourier (giantSignedChronologicalJoinedOffset h κ (Fin.last n)) (θ : AddCircle (1 : ℝ)) *
        ∏ i, (giantTwoSidedResidueDamping PS (k+ell) q (giantSignedChronologicalSmallSource h i).val.1 : ℂ) *
          (giantTwoSidedResidueDamping PS (k+ell) q (giantSignedChronologicalSmallTarget h i).val.1 : ℂ) := by
  have hK (i : Fin n) :
      giantSignedJoinedCoefficient (PS := PS) (K i)
        (giantTwoSidedPermuteLabels (giantSignedChronologicalJoinedSourcePermutation h i)
          (giantSignedChronologicalJoinedLabels h i.castSucc))
        (giantTwoSidedPermuteLabels (giantSignedChronologicalJoinedTargetPermutation h i)
          (giantSignedChronologicalJoinedLabels h i.succ))
        (giantSignedChronologicalJoinedAuxiliary h i) =
      K i (giantSignedChronologicalBigSource h i) (giantSignedChronologicalBigTarget h i) (h.auxiliary i) := rfl
  have hslot : ((giantTwoSidedResidueSlotNormalization (J := S ⊕ B) (k+ell) : ℂ) ^ n) =
      ∏ _i : Fin n, (giantTwoSidedResidueSlotNormalization (J := S) (k+ell) : ℂ) *
        (giantTwoSidedResidueSlotNormalization (J := B) (k+ell) : ℂ) := by
    rw [giantTwoSidedResidueSlotNormalization_sum, Complex.ofReal_mul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hslot, ← giantSignedChronologicalReturnPhase_eq h κ θ,
    giantSignedChronologicalBandNormalization_eq_original]
  unfold giantSignedChronologicalExterior giantSignedChronologicalEdgeExterior
    giantSignedChronologicalOriginalRootScalar giantTwoSidedRootScalar
  rw [giantTwoSidedResidueHaarStateMass_eq, joined_marked_mass (PS := PS) (PB := PB)]
  simp_rw [giantSignedChronologicalJoinedAuxiliaryMass_eq, joined_fresh_mass (PS := PS) (PB := PB) (ell := ell),
    hK, giantSignedChronologicalJoinedDilation_eq]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, ofReal_product,
    div_eq_mul_inv, Finset.prod_mul_distrib]
  ac_rfl

end
end ArtinMatthews
