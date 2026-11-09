module

public import ArtinMatthews.MarkedMajorCharacterArc


set_option backward.privateInPublic true
@[expose] public section

/-! The actual unseparated source coefficients and their six-character
twists. Unit support follows from the genuine centered/rough definitions. -/
namespace ArtinMatthews
open Finset ComplexConjugate
noncomputable section

def markedMajorBareTripleCoefficient {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y W modulation : ℝ)
    (β : ℕ → ℂ) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  cutoff ((z.1:ℝ)/Y)*(markedMajorLabelMass bands:ℂ)*
    markedMajorCenteredCoefficient W modulation z.2.1*β z.2.2

def markedMajorBareConjugateTripleCoefficient {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y W modulation : ℝ)
    (β : ℕ → ℂ) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  cutoff ((z.1:ℝ)/Y)*(markedMajorLabelMass bands:ℂ)*
    conj (markedMajorCenteredCoefficient W modulation z.2.1)*β z.2.2

theorem markedMajorBareConjugateTripleCoefficient_eq {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y W modulation : ℝ) (β : ℕ → ℂ) :
    markedMajorBareConjugateTripleCoefficient bands cutoff Y W modulation β =
      markedMajorBareTripleCoefficient bands cutoff Y W (-modulation) β := by
  funext z
  simp only [markedMajorBareConjugateTripleCoefficient,markedMajorBareTripleCoefficient,
    marked_centered_coefficient_conj]

theorem markedMajor_bare_left_twist {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y W modulation θ : ℝ)
    (β : ℕ → ℂ) (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (z : ℕ×(ℕ×ℕ)) :
    markedMajorBareTripleCoefficient bands cutoff Y W modulation β z*
      markedMajorLabelArcPhase θ Y z.1*markedMajorCharacterLeft q χ z =
      markedMajorLabelTripleCoefficient bands cutoff (markedCoordinateDirichlet q χ 1) θ Y
        (markedCoordinateDirichlet q χ 2) W modulation (fun n => β n*markedCoordinateDirichlet q χ 3 n) z := by
  unfold markedMajorBareTripleCoefficient markedMajorLabelArcPhase markedMajorCharacterLeft
    markedMajorLabelTripleCoefficient markedMajorLabelWeight
  ring

theorem markedMajor_bare_right_twist {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y W modulation θ : ℝ)
    (β : ℕ → ℂ) (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (z : ℕ×(ℕ×ℕ)) :
    markedMajorBareConjugateTripleCoefficient bands cutoff Y W modulation β z*
      markedMajorLabelArcPhase (-θ) Y z.1*markedMajorCharacterRight q χ z =
      markedMajorLabelConjugateTripleCoefficient bands cutoff (markedCoordinateDirichlet q χ 0) (-θ) Y
        (markedCoordinateDirichlet q χ 4) W modulation (fun n => β n*markedCoordinateDirichlet q χ 5 n) z := by
  unfold markedMajorBareConjugateTripleCoefficient markedMajorLabelArcPhase markedMajorCharacterRight
    markedMajorLabelConjugateTripleCoefficient markedMajorLabelWeight
  ring

theorem markedMajor_bare_unit_support {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    (cutoff : ℝ → ℂ) (Y W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (q : ℕ) [NeZero q] (hq : (q:ℝ) ≤ W) (hWu : W ≤ u)
    (hbandsq : ∀ j p,p ∈ bands j → q < p)
    (hβrough : ∀ n ∈ Icc l r,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊W⌋₊,¬p∣n)
    (z : ℕ×(ℕ×ℕ)) (hz : z ∈ markedMajorLabelTripleSet bands u v l r)
    (hcoeff : markedMajorBareTripleCoefficient bands cutoff Y W modulation β z ≠ 0) :
    IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q) := by
  obtain ⟨hs,hm,hn⟩ := by simpa only [markedMajorLabelTripleSet,mem_product] using hz
  have hα : markedMajorCenteredCoefficient W modulation z.2.1 ≠ 0 := by
    intro hzero
    exact hcoeff (by simp only [markedMajorBareTripleCoefficient,hzero,mul_zero,zero_mul])
  have hβ : β z.2.2 ≠ 0 := by
    intro hzero
    exact hcoeff (by simp only [markedMajorBareTripleCoefficient,hzero,mul_zero])
  have hu0 : 0 ≤ u := (Nat.cast_nonneg q).trans (hq.trans hWu)
  have hmW : W < (z.2.1:ℝ) := hWu.trans_lt ((Nat.floor_lt hu0).mp (mem_Ioc.mp hm).1)
  exact ⟨marked_label_isUnit bands hbands hbandsq hs,
    marked_centered_nonzero_isUnit W modulation hq hmW hα,
    marked_rough_isUnit W hq (hβrough _ hn hβ)⟩

theorem markedMajor_bare_conjugate_unit_support {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    (cutoff : ℝ → ℂ) (Y W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (q : ℕ) [NeZero q] (hq : (q:ℝ) ≤ W) (hWu : W ≤ u)
    (hbandsq : ∀ j p,p ∈ bands j → q < p)
    (hβrough : ∀ n ∈ Icc l r,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊W⌋₊,¬p∣n)
    (z : ℕ×(ℕ×ℕ)) (hz : z ∈ markedMajorLabelTripleSet bands u v l r)
    (hcoeff : markedMajorBareConjugateTripleCoefficient bands cutoff Y W modulation β z ≠ 0) :
    IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q) := by
  rw [markedMajorBareConjugateTripleCoefficient_eq] at hcoeff
  exact markedMajor_bare_unit_support bands hbands cutoff Y W (-modulation) u v l r β q hq hWu hbandsq hβrough z hz hcoeff

theorem markedMajor_character_twisted_coefficient_bound (β : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ) {B : ℝ} (hn : ‖β n‖ ≤ B) :
    ‖β n*χ n‖ ≤ B := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (χ.norm_le_one n) (norm_nonneg _)).trans (by simpa only [mul_one] using hn)

end
end ArtinMatthews
