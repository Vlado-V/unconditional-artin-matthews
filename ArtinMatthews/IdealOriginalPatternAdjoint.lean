module

public import ArtinMatthews.IdealPatternPairing


set_option backward.privateInPublic true
@[expose] public section

/-! Reversal of the actual original harmonic copied/fresh pattern.
The joint law is preserved by swapping the free coordinates of the two labels. -/
namespace ArtinMatthews

open Finset
open scoped BigOperators ComplexConjugate

noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealDilationPhase_reverse (Θ ζ : ℝ) (D : ℕ) :
    idealDilationPhase (-Θ) (-ζ) D = star (idealDilationPhase Θ ζ D) := by
  have harg : (D : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg D)]
    exact ne_of_lt Real.pi_pos
  have hpow : conj ((D : ℂ) ^ ((ζ : ℂ) * Complex.I)) =
      (D : ℂ) ^ (((-ζ : ℝ) : ℂ) * Complex.I) := by
    have he := (Complex.cpow_conj (D : ℂ) ((ζ : ℂ) * Complex.I) harg).symm
    simpa only [map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg, mul_neg, neg_mul] using he
  have hadd : conj (idealAdditivePhase Θ D) = idealAdditivePhase (-Θ) D := by
    unfold idealAdditivePhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  unfold idealDilationPhase
  rw [Complex.star_def, map_mul, hpow, hadd]

private theorem idealAdjointLabelExpectation_conj {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (F : MarkedPhysicalMarking P M → ℂ) :
    conj (idealLabelExpectation P M F) = idealLabelExpectation P M (fun a => conj (F a)) := by
  unfold idealLabelExpectation
  change conj (∑ a, (idealLabelMass P M a : ℂ) * F a) =
    ∑ a, (idealLabelMass P M a : ℂ) * conj (F a)
  simp only [map_sum, map_mul, Complex.conj_ofReal]

theorem idealPattern_reverse_pairing {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (C : G → Finset (Fin k)) (Θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (f g : MarkedPhysicalMarking P (k + ell) → ℂ) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) C (-Θ) (-ζ) (fun a b aux => star (K b a aux)) g) =
      star (idealLabelPairing P g (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
        (fun j => markedHarmonicAtom (P j)) C Θ ζ K f)) := by
  let S := idealPatternFreeCoordinates (ell := ell) C
  have hback (a b : MarkedPhysicalMarking P (k + ell)) :
      idealMix S (idealMix S a b) (idealMix S b a) = a :=
    congrArg Prod.fst ((idealMixEquiv (P := P) S).left_inv (a, b))
  have hcopied (a b : MarkedPhysicalMarking P (k + ell)) :
      giantTwoSidedPatternCopiedProduct C (idealMix S a b) = giantTwoSidedPatternCopiedProduct C a := by
    apply giantTwoSidedPatternCopiedProduct_eq
    intro j i hi
    have hnot : (j, Fin.castAdd ell i) ∉ S :=
      fun hmem => hi ((idealPatternFreeCoordinates_first C j i).mp hmem)
    simp only [idealMix, hnot, ite_false]
  rw [idealPatternPairing_expectation P hV C (-Θ) (-ζ) (fun a b aux => star (K b a aux)) f g,
    idealPatternPairing_expectation P hV C Θ ζ K g f, Complex.star_def, map_sum]
  apply sum_congr rfl
  intro aux _
  rw [map_mul, Complex.conj_ofReal]
  simp_rw [idealAdjointLabelExpectation_conj]
  congr 1
  let Q (a b : MarkedPhysicalMarking P (k + ell)) : ℂ :=
    conj (star (g a) * K a (idealMix S a b) aux *
      idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct C a *
        giantTwoSidedPatternAuxiliaryProduct aux) * f (idealMix S a b))
  change _ = idealLabelExpectation P (k + ell) (fun a => idealLabelExpectation P (k + ell) (Q a))
  rw [← idealLabelExpectation_swap P S Q]
  apply congrArg (idealLabelExpectation P (k + ell))
  funext a
  apply congrArg (idealLabelExpectation P (k + ell))
  funext b
  dsimp only [Q]
  rw [hback a b, hcopied a b, idealDilationPhase_reverse]
  simp only [← Complex.star_def, star_mul, star_star]
  ring

end
end ArtinMatthews
