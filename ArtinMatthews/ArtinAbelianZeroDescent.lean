module

public import ArtinMatthews.ArtinAbelianContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! Zero transfer through the proved abelian factorization, preserving the
actual zeta pole and every modulus-prime correction. -/
noncomputable section
namespace ArtinMatthews.AbelianLocal
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField IsMulCommutative Classical BigOperators

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]
variable {N : ℕ} [NeZero N]

local instance descentArtinCharactersFintype : Fintype (Gal(E/F) →* ℂˣ) := Fintype.ofFinite _

theorem abelianArtinContinuedFactor_ne_zero_iff
    (χ : Gal(E/F) →* ℂˣ) (ψ : EvenRayCharacter F N) {s : ℂ} (hs : 0 < s.re) :
    abelianArtinContinuedFactor F E χ ψ s ≠ 0 ↔ ψ.nonprincipalContinued s ≠ 0 := by
  rw [abelianArtinContinuedFactor, mul_ne_zero_iff]
  exact and_iff_right (abelianArtinFiniteCorrection_ne_zero F E χ _ hs)

theorem abelianArtinRelativeContinued_ne_zero_iff
    (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N) {s : ℂ} (hs : 0 < s.re) :
    abelianArtinRelativeContinued F E ψ s ≠ 0 ↔
      ∀ χ, χ ≠ 1 → (ψ χ).nonprincipalContinued s ≠ 0 := by
  rw [abelianArtinRelativeContinued, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true,
    abelianArtinContinuedFactor_ne_zero_iff F E _ _ hs]

variable (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N)
variable (hψ : ∀ χ, (ψ χ).idealHom = GaloisIdealCharacter.idealHom F E χ)
variable (hD : (NumberField.discr E).natAbs ∣ N)
variable (hnp : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)

include hψ hD hnp

/-- Zero-freeness of the full auxiliary zeta is equivalent to zero-freeness
of the base zeta and its actual nonprincipal ray factors. -/
theorem regularizedDedekindZeta_ne_zero_iff {s : ℂ} (hs : 0 < s.re) :
    mixedRegularizedDedekindZeta E s ≠ 0 ↔
      mixedRegularizedDedekindZeta F s ≠ 0 ∧
        ∀ χ, χ ≠ 1 → (ψ χ).nonprincipalContinued s ≠ 0 := by
  rw [regularizedDedekindZeta_eq_mul_abelianArtinRelativeContinued F E ψ hψ hD hnp hs,
    mul_ne_zero_iff, abelianArtinRelativeContinued_ne_zero_iff F E ψ hs]

theorem continuedDedekindZeta_base_ne_zero {s : ℂ} (hs : 0 < s.re)
    (he : mixedDedekindZetaContinuation E s ≠ 0) :
    mixedDedekindZetaContinuation F s ≠ 0 := by
  rw [continuedDedekindZeta_eq_mul_abelianArtinRelativeContinued F E ψ hψ hD hnp hs] at he
  exact (mul_ne_zero_iff.mp he).1

/-- The nonprincipal Artin factors cannot vanish at one: the actual simple
poles of the two Dedekind zeta functions have nonzero class-number residues. -/
theorem artinRay_nonprincipalContinued_one_ne_zero
    (χ : Gal(E/F) →* ℂˣ) (hχ : χ ≠ 1) : (ψ χ).nonprincipalContinued 1 ≠ 0 := by
  have h := (regularizedDedekindZeta_ne_zero_iff F E ψ hψ hD hnp
    (s := 1) (by norm_num)).mp (mixedRegularizedDedekindZeta_one_ne_zero E)
  exact h.2 χ hχ

/-- The finite product of continued nonprincipal Artin factors at one is the
ratio of the actual Dedekind class-number residues. -/
theorem abelianArtinRelativeContinued_one_eq_residue_ratio :
    abelianArtinRelativeContinued F E ψ 1 =
      (NumberField.dedekindZeta_residue E : ℂ) / (NumberField.dedekindZeta_residue F : ℂ) := by
  have h := regularizedDedekindZeta_eq_mul_abelianArtinRelativeContinued F E ψ hψ hD hnp
    (s := 1) (by norm_num)
  rw [mixedRegularizedDedekindZeta_one, mixedRegularizedDedekindZeta_one] at h
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_ne_zero F))).mpr
  simpa only [mul_comm] using h.symm

end ArtinMatthews.AbelianLocal
