module

public import OAI.NumberTheory.DirichletL.Hecke.Family
public import OAI.NumberTheory.DirichletL.IdealCharacter
public import OAI.NumberTheory.DirichletL.Arithmetic.LatticeCount
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace


set_option backward.privateInPublic true
@[expose] public section

/-!
# Actual ideal coefficients for an Eisenstein Hecke theta series

The coefficient of index `n` is the finite sum of the ideal character over
integral ideals of absolute norm `n`. This file constructs those coefficients
from a genuine unit-invariant residue character; it does not assert modularity
or the existence of a cusp form.
-/

noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths

namespace ArtinMatthews

open HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- The ideal character attached to a unit-invariant residue character of the
Eisenstein integers, extended by zero on the zero ideal and at its conductor. -/
def thetaIdealCharacter (χ : Character) : Ideal O →*₀ ℂ :=
  IdealCharacter.ofResidue χ.modulus χ.residue χ.unit_trivial

/-- The finite family of integral ideals with prescribed absolute norm. -/
def idealsOfNorm (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

@[simp] theorem mem_idealsOfNorm {I : Ideal O} {n : ℕ} :
    I ∈ idealsOfNorm n ↔ I.absNorm = n := by
  simp [idealsOfNorm]

/-- The actual ideal-sum coefficient of the Hecke theta series. -/
def idealThetaCoeff (χ : Character) (n : ℕ) : ℂ :=
  ∑ I ∈ idealsOfNorm n, thetaIdealCharacter χ I

@[simp] theorem thetaIdealCharacter_zero (χ : Character) :
    thetaIdealCharacter χ 0 = 0 := map_zero _

@[simp] theorem thetaIdealCharacter_one (χ : Character) :
    thetaIdealCharacter χ 1 = 1 := map_one _

theorem thetaIdealCharacter_span (χ : Character) {z : O} (hz : z ≠ 0) :
    thetaIdealCharacter χ (Ideal.span {z}) = elementCoeff χ z :=
  IdealCharacter.ofResidue_span χ.modulus χ.residue χ.unit_trivial hz

theorem thetaIdealCharacter_norm_le_one (χ : Character) (I : Ideal O) :
    ‖thetaIdealCharacter χ I‖ ≤ 1 := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact IdealCharacter.norm_ofResidue_le_one χ.modulus χ.residue χ.unit_trivial I

@[simp] theorem idealThetaCoeff_zero (χ : Character) : idealThetaCoeff χ 0 = 0 := by
  have hideals : idealsOfNorm 0 = {0} := by
    ext I
    simp [Ideal.absNorm_eq_zero_iff]
  rw [idealThetaCoeff, hideals, Finset.sum_singleton]
  exact map_zero _

/-- Triangle inequality on the genuine finite ideal norm fiber. -/
theorem idealThetaCoeff_norm_le_card (χ : Character) (n : ℕ) :
    ‖idealThetaCoeff χ n‖ ≤ ((idealsOfNorm n).card : ℝ) := by
  unfold idealThetaCoeff
  calc
    _ ≤ ∑ I ∈ idealsOfNorm n, ‖thetaIdealCharacter χ I‖ := norm_sum_le _ _
    _ ≤ ∑ _I ∈ idealsOfNorm n, (1 : ℝ) :=
      Finset.sum_le_sum fun I _ => thetaIdealCharacter_norm_le_one χ I
    _ = _ := by simp

/-- Ideals of a fixed norm are no more numerous than a bounded Eisenstein
lattice region: choose one generator for each principal ideal. -/
theorem idealsOfNorm_card_le (n : ℕ) :
    (idealsOfNorm n).card ≤ 64 * (n + 1) := by
  classical
  let gen : Ideal O → O := fun I => Submodule.IsPrincipal.generator I
  have hgen : Function.Injective gen := by
    intro I J h
    calc
      I = Ideal.span {gen I} := (Ideal.span_singleton_generator I).symm
      _ = Ideal.span {gen J} := by rw [h]
      _ = J := Ideal.span_singleton_generator J
  have hcount := ShortDraftLatticeCount.actual_eisenstein_count
    ((idealsOfNorm n).image gen) n (by
      intro z hz
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hz
      have heq : ShortDraftLatticeCount.qNat (gen I) = n := by
        rw [ActualEisensteinCubic.qNat_eq_absNorm_span,
          Ideal.span_singleton_generator, mem_idealsOfNorm.mp hI]
      have heq' := congrArg (fun m : ℕ => (m : ℤ)) heq
      simpa only [ShortDraftLatticeCount.qNat,
        Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg (gen I))] using heq'.le)
  rwa [Finset.card_image_of_injective _ hgen] at hcount

/-- A proved polynomial bound for the actual ideal-sum coefficients. This is
sufficient for convergence of the associated holomorphic q-series. -/
theorem idealThetaCoeff_norm_le (χ : Character) (n : ℕ) :
    ‖idealThetaCoeff χ n‖ ≤ 64 * ((n : ℝ) + 1) := by
  apply (idealThetaCoeff_norm_le_card χ n).trans
  exact_mod_cast idealsOfNorm_card_le n

@[simp] theorem idealThetaCoeff_one (χ : Character) : idealThetaCoeff χ 1 = 1 := by
  have hideals : idealsOfNorm 1 = {1} := by
    ext I
    simp [Ideal.absNorm_eq_one_iff]
  rw [idealThetaCoeff, hideals, Finset.sum_singleton]
  exact map_one _

/-- A ring automorphism preserves the actual finite quotient cardinality,
hence the absolute norm of an ideal. -/
theorem ideal_absNorm_map_ringEquiv (σ : O ≃+* O) (I : Ideal O) :
    (I.map σ.toRingHom).absNorm = I.absNorm := by
  change Nat.card (O ⧸ I.map σ.toRingHom) = Nat.card (O ⧸ I)
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map σ.toRingHom) σ rfl).symm.toEquiv

/-- Reindexing the actual norm fiber by a ring automorphism. -/
theorem idealThetaCoeff_reindex (χ : Character) (σ : O ≃+* O) (n : ℕ) :
    (∑ I ∈ idealsOfNorm n, thetaIdealCharacter χ (I.map σ.toRingHom)) =
      idealThetaCoeff χ n := by
  classical
  unfold idealThetaCoeff
  apply Finset.sum_bij (fun I _ => I.map σ.toRingHom)
  · intro I hI
    exact mem_idealsOfNorm.mpr ((ideal_absNorm_map_ringEquiv σ I).trans
      (mem_idealsOfNorm.mp hI))
  · intro I _ J _ h
    have h' := congrArg (fun M : Ideal O => M.map σ.symm.toRingHom) h
    simpa using h'
  · intro I hI
    refine ⟨I.map σ.symm.toRingHom, ?_, ?_⟩
    · exact mem_idealsOfNorm.mpr ((ideal_absNorm_map_ringEquiv σ.symm I).trans
        (mem_idealsOfNorm.mp hI))
    · exact Ideal.map_of_equiv σ.symm
  · intro _ _
    rfl

/-- The paper's conjugation condition on the ideal character implies that
all of the actual ideal-sum coefficients are real. The norm-fiber permutation
is proved by reindexing and is not an assumed coefficient identity. -/
theorem idealThetaCoeff_conj_of_ideal_conjugation (χ : Character) (σ : O ≃+* O)
    (hχ : ∀ I : Ideal O, thetaIdealCharacter χ (I.map σ.toRingHom) =
      star (thetaIdealCharacter χ I)) (n : ℕ) :
    star (idealThetaCoeff χ n) = idealThetaCoeff χ n := by
  rw [idealThetaCoeff, star_sum]
  simp_rw [← hχ]
  exact idealThetaCoeff_reindex χ σ n

theorem idealThetaCoeff_re_of_ideal_conjugation (χ : Character) (σ : O ≃+* O)
    (hχ : ∀ I : Ideal O, thetaIdealCharacter χ (I.map σ.toRingHom) =
      star (thetaIdealCharacter χ I)) (n : ℕ) :
    ((idealThetaCoeff χ n).re : ℂ) = idealThetaCoeff χ n :=
  Complex.conj_eq_iff_re.mp (idealThetaCoeff_conj_of_ideal_conjugation χ σ hχ n)

end ArtinMatthews
