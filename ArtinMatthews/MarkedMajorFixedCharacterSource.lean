module

public import ArtinMatthews.MarkedMajorCharacterSource
public import ArtinMatthews.HeckeDirichletProduct
public import ArtinMatthews.GiantFixedCharacterReplacement


set_option backward.privateInPublic true
@[expose] public section

/-! The external fixed character multiplies the ordinary centered
coefficient. Its rational-arc twists are literal product-modulus
characters, including at nonunits. -/
namespace ArtinMatthews
open Finset
noncomputable section

def markedMajorFixedBareTripleCoefficient {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y W modulation : ℝ)
    (β : ℕ → ℂ) {M : ℕ} (ξ : DirichletCharacter ℂ M) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  markedMajorBareTripleCoefficient bands cutoff Y W modulation β z*ξ (z.2.1*z.2.2)

def markedMajorFixedBareConjugateTripleCoefficient {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y W modulation : ℝ)
    (β : ℕ → ℂ) {M : ℕ} (ξ : DirichletCharacter ℂ M) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  markedMajorBareConjugateTripleCoefficient bands cutoff Y W modulation β z*ξ (z.2.1*z.2.2)

theorem markedMajor_fixed_bare_left_twist {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y W modulation θ : ℝ)
    (β : ℕ → ℂ) {M : ℕ} (ξ : DirichletCharacter ℂ M)
    (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (z : ℕ×(ℕ×ℕ)) :
    markedMajorFixedBareTripleCoefficient bands cutoff Y W modulation β ξ z*
      markedMajorLabelArcPhase θ Y z.1*markedMajorCharacterLeft q χ z =
      markedMajorLabelTripleCoefficient bands cutoff (markedCoordinateDirichlet q χ 1) θ Y
        (heckeDirichletProduct ξ (markedCoordinateDirichlet q χ 2)) W modulation
        (fun n => ξ n*(β n*markedCoordinateDirichlet q χ 3 n)) z := by
  unfold markedMajorFixedBareTripleCoefficient markedMajorBareTripleCoefficient
    markedMajorLabelTripleCoefficient markedMajorLabelWeight markedMajorLabelArcPhase
    markedMajorCharacterLeft
  rw [heckeDirichletProduct_natCast,map_mul]
  ring

theorem markedMajor_fixed_bare_right_twist {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y W modulation θ : ℝ)
    (β : ℕ → ℂ) {M : ℕ} (ξ : DirichletCharacter ℂ M)
    (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (z : ℕ×(ℕ×ℕ)) :
    markedMajorFixedBareConjugateTripleCoefficient bands cutoff Y W modulation β ξ z*
      markedMajorLabelArcPhase (-θ) Y z.1*markedMajorCharacterRight q χ z =
      markedMajorLabelConjugateTripleCoefficient bands cutoff (markedCoordinateDirichlet q χ 0) (-θ) Y
        (heckeDirichletProduct ξ (markedCoordinateDirichlet q χ 4)) W modulation
        (fun n => ξ n*(β n*markedCoordinateDirichlet q χ 5 n)) z := by
  unfold markedMajorFixedBareConjugateTripleCoefficient markedMajorBareConjugateTripleCoefficient
    markedMajorLabelConjugateTripleCoefficient markedMajorLabelWeight markedMajorLabelArcPhase
    markedMajorCharacterRight
  rw [heckeDirichletProduct_natCast,map_mul]
  ring

theorem markedMajor_fixed_bare_unit_support {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p∈bands j → p.Prime)
    (cutoff : ℝ → ℂ) (Y W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    {M : ℕ} (ξ : DirichletCharacter ℂ M) (q : ℕ) [NeZero q]
    (hq : (q:ℝ) ≤ W) (hWu : W ≤ u) (hbandsq : ∀ j p,p∈bands j → q<p)
    (hβrough : ∀ n∈Icc l r,β n≠0 → ∀ p∈Nat.primesLE ⌊W⌋₊,¬p∣n)
    (z : ℕ×(ℕ×ℕ)) (hz : z∈markedMajorLabelTripleSet bands u v l r)
    (hcoeff : markedMajorFixedBareTripleCoefficient bands cutoff Y W modulation β ξ z≠0) :
    IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q) :=
  markedMajor_bare_unit_support bands hbands cutoff Y W modulation u v l r β q hq hWu
    hbandsq hβrough z hz (mul_ne_zero_iff.mp hcoeff).1

theorem markedMajor_fixed_bare_conjugate_unit_support {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p∈bands j → p.Prime)
    (cutoff : ℝ → ℂ) (Y W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    {M : ℕ} (ξ : DirichletCharacter ℂ M) (q : ℕ) [NeZero q]
    (hq : (q:ℝ) ≤ W) (hWu : W ≤ u) (hbandsq : ∀ j p,p∈bands j → q<p)
    (hβrough : ∀ n∈Icc l r,β n≠0 → ∀ p∈Nat.primesLE ⌊W⌋₊,¬p∣n)
    (z : ℕ×(ℕ×ℕ)) (hz : z∈markedMajorLabelTripleSet bands u v l r)
    (hcoeff : markedMajorFixedBareConjugateTripleCoefficient bands cutoff Y W modulation β ξ z≠0) :
    IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q) :=
  markedMajor_bare_conjugate_unit_support bands hbands cutoff Y W modulation u v l r β q hq hWu
    hbandsq hβrough z hz (mul_ne_zero_iff.mp hcoeff).1

end
end ArtinMatthews
