module

public import ArtinMatthews.IdealLabelOperator
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

/-! The original auxiliary law and the literal derivative/Fourier multiplier. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}

omit [DecidableEq J] in
theorem giantSignedIdealAuxiliaryMass_nonneg
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (aux : GiantTwoSidedPatternAuxiliary P C) :
    0 ≤ idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux :=
  Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun _i _ =>
    markedHarmonicAtom_nonneg (P j) (hV j)

theorem giantSignedIdealAuxiliaryMass_sum
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k)) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P C,
      idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux) = 1 := by
  classical
  unfold idealAuxiliaryMass
  rw [← Fintype.prod_sum (fun j (a : C j → P j) => ∏ i, markedHarmonicAtom (P j) (a i))]
  have hj (j : J) : (∑ a : C j → P j, ∏ i, markedHarmonicAtom (P j) (a i)) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : C j) (p : P j) => markedHarmonicAtom (P j) p)]
    simp only [markedHarmonicAtom_sum (P j) (hV j), Finset.prod_const_one]
  simp only [hj, Finset.prod_const_one]

omit [DecidableEq J] in
theorem giantSignedIdealMultiplier_norm
    (hP : ∀ j p, p ∈ P j → p.Prime) (C : J → Finset (Fin k))
    (Θ ζ : ℝ) (a : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P C) :
    ‖((giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux : ℕ) : ℂ) ^
      ((ζ : ℂ) * Complex.I) *
      idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)‖ = 1 := by
  classical
  have hD : 0 < giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux :=
    Nat.mul_pos (Finset.prod_pos fun j _ => Finset.prod_pos fun i _ =>
      (hP j _ (a j (Fin.castAdd ell i)).property).pos)
      (Finset.prod_pos fun j _ => Finset.prod_pos fun i _ => (hP j _ (aux j i).property).pos)
  rw [norm_mul, idealAdditivePhase_norm, mul_one, Complex.norm_natCast_cpow_of_pos hD]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    mul_zero, zero_mul, sub_self, Real.rpow_zero]

def giantSignedIdealAveragedMultiplier (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (a b : MarkedPhysicalMarking P (k+ell)) : ℂ :=
  ∑ aux : GiantTwoSidedPatternAuxiliary P C,
    (idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux : ℂ) * K a b aux *
      (((giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux : ℕ) : ℂ) ^
        ((ζ : ℂ) * Complex.I) *
        idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux))

theorem giantSignedIdealAveragedMultiplier_norm
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (C : J → Finset (Fin k)) (Θ ζ R : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ R) (a b : MarkedPhysicalMarking P (k+ell)) :
    ‖giantSignedIdealAveragedMultiplier C Θ ζ K a b‖ ≤ R := by
  classical
  unfold giantSignedIdealAveragedMultiplier
  calc
    _ ≤ ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        ‖(idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux : ℂ) * K a b aux *
          (((giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux : ℕ) : ℂ) ^
            ((ζ : ℂ) * Complex.I) *
            idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux * R := by
      apply Finset.sum_le_sum
      intro aux _
      rw [norm_mul, norm_mul, giantSignedIdealMultiplier_norm hP,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (giantSignedIdealAuxiliaryMass_nonneg hV C aux), mul_one]
      exact mul_le_mul_of_nonneg_left (hK a b aux) (giantSignedIdealAuxiliaryMass_nonneg hV C aux)
    _ = R := by rw [← Finset.sum_mul, giantSignedIdealAuxiliaryMass_sum hV C, one_mul]

end
end ArtinMatthews
