module

public import ArtinMatthews.QuadraticHeckeSmallResidue
public import ArtinMatthews.SourceQuadraticMaskedCutoff
public import ArtinMatthews.SourceQuadraticPairConductor
public import ArtinMatthews.SourceQuadraticBlockIdeals
public import Mathlib.Analysis.MellinTransform


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀
local notation "C" => sourceQuadraticConductor F S₀ hζ

/-- A squarefree column has disjoint common and residual prime supports. -/
theorem sourceQuadratic_common_coprime_quotient (b g : E)
    (hb : sourceReflectionIsSquarefree b) : IsCoprime (I g) (I (b - g)) := by
  rw [sourceQuadraticBlock_ideal_coprime_iff,
    sourceQuadraticExteriorQuotient_support F S₀ b g hb]
  apply Finset.disjoint_left.mpr
  intro P hPg hPq
  exact (Finset.mem_sdiff.mp hPq).2 hPg

/-- The fixed and common modulus is disjoint from both squarefree residual ideals. -/
theorem sourceQuadratic_commonModulus_coprime_residualProduct (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c) :
    IsCoprime (Bad * I g) (I (b - g) * I (c - g)) := by
  exact ((sourceQuadraticBlock_exterior_coprime F S₀ (b - g)).symm.mul_left
    (sourceQuadratic_common_coprime_quotient F S₀ b g hb)).mul_right
      ((sourceQuadraticBlock_exterior_coprime F S₀ (c - g)).symm.mul_left
        (sourceQuadratic_common_coprime_quotient F S₀ c g hc))

/-- The conductor in an actual common-ideal pair is coprime to the common ideal. -/
theorem sourceQuadraticPair_common_coprime_conductor (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    IsCoprime (I g) (C ((b - g) + (c - g))) := by
  rw [sourceQuadraticPairConductor_eq_product F S₀ hζ b c g hb hc hg hclass]
  exact (sourceQuadratic_common_coprime_quotient F S₀ b g hb).mul_right
    (sourceQuadratic_common_coprime_quotient F S₀ c g hc)

/-- The common ideal factors out of the full small-square contour density. -/
theorem sourceQuadraticSmallModulus_density (g e : E) (hgc : IsCoprime (I g) (C e)) :
    quadraticHeckeCoprimeDensity F (Bad * I g * C e) =
      quadraticHeckeCoprimeDensity F (Bad * C e) * quadraticHeckeCoprimeDensity F (I g) := by
  have hBad : Bad ≠ ⊥ := by
    unfold sourceQuadraticBlockBadIdeal
    exact Ideal.span_singleton_eq_bot.not.mpr
      (principalizingDenominator_ne_zero (sourceHilbertSeed F S₀))
  have hcop : IsCoprime (I g) (Bad * C e) :=
    (sourceQuadraticBlock_exterior_coprime F S₀ g).mul_right hgc
  rw [show Bad * I g * C e = (Bad * C e) * I g by ac_rfl]
  exact quadraticHeckeCoprimeDensity_mul F
    (mul_ne_zero hBad (sourceQuadraticConductor_ne_bot F S₀ hζ e))
    (sourcePrimeExponentIdeal_ne_bot F S₀ g) hcop.symm

/-- The common residue scalar in the original and dual square-norm contours. -/
def sourceQuadraticSmallResidueFactor (M : ℝ) : ℂ :=
  (dedekindZeta_residue F : ℂ) * (Real.sqrt M : ℂ) *
    ((1 / 2 : ℂ) * mellin (fun t : ℝ => (sourceQuadraticB2Bump t : ℂ)) (1 / 2))

variable [IsTotallyComplex F]
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ

/-- The actual small-contour residue is the masked half-coefficient cutoff. -/
theorem sourceQuadraticSmallResidue_eq_halfCoefficient (g e : E)
    (hgc : IsCoprime (I g) (C e)) {M : ℝ} (hM : 0 < M) (H : ℝ) :
    (∑' a : {J : Ideal (𝓞 F) // Squarefree J},
      if IsCoprime a.val Bad ∧ IsCoprime a.val (I g) ∧ (Ideal.absNorm a.val : ℝ) ≤ H then
        (Ψ e).allCoefficient a.val *
          ((dedekindZeta_residue F : ℂ) *
            (Real.sqrt (M / (Ideal.absNorm a.val : ℝ)) : ℂ) *
            ((1 / 2 : ℂ) * mellin (fun t : ℝ => (sourceQuadraticB2Bump t : ℂ)) (1 / 2)) *
            quadraticHeckeCoprimeDensity F (Bad * I g * C e)) else 0) =
      sourceQuadraticSmallResidueFactor F M *
        quadraticHeckeCoprimeDensity F (Bad * C e) * quadraticHeckeCoprimeDensity F (I g) *
        ∑ a ∈ quadraticHeckeCoprimeCutoff F (I g) H,
          if IsCoprime a Bad then quadraticHeckeHalfCoefficient F (Ψ e) a else 0 := by
  rw [sourceQuadraticSmallModulus_density F S₀ hζ g e hgc]
  have h := quadraticHeckeSmallResidue_sum F (Ψ e) (I g) Bad hM.le H
    (dedekindZeta_residue F : ℂ)
    (((1 / 2 : ℂ) * mellin (fun t : ℝ => (sourceQuadraticB2Bump t : ℂ)) (1 / 2)) *
      quadraticHeckeCoprimeDensity F (Bad * I g * C e))
  rw [sourceQuadraticSmallModulus_density F S₀ hζ g e hgc] at h
  simpa only [sourceQuadraticSmallResidueFactor, mul_assoc] using h

/-- The class-sliced common pair supplies the exact coprimality needed for the residue identity. -/
theorem sourceQuadraticSmallResidue_commonPair (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    {M : ℝ} (hM : 0 < M) (H : ℝ) :
    (∑' a : {J : Ideal (𝓞 F) // Squarefree J},
      if IsCoprime a.val Bad ∧ IsCoprime a.val (I g) ∧ (Ideal.absNorm a.val : ℝ) ≤ H then
        (Ψ ((b - g) + (c - g))).allCoefficient a.val *
          ((dedekindZeta_residue F : ℂ) *
            (Real.sqrt (M / (Ideal.absNorm a.val : ℝ)) : ℂ) *
            ((1 / 2 : ℂ) * mellin (fun t : ℝ => (sourceQuadraticB2Bump t : ℂ)) (1 / 2)) *
            quadraticHeckeCoprimeDensity F (Bad * I g * C ((b - g) + (c - g)))) else 0) =
      sourceQuadraticSmallResidueFactor F M *
        quadraticHeckeCoprimeDensity F (Bad * C ((b - g) + (c - g))) *
        quadraticHeckeCoprimeDensity F (I g) *
        ∑ a ∈ quadraticHeckeCoprimeCutoff F (I g) H,
          if IsCoprime a Bad then
            quadraticHeckeHalfCoefficient F (Ψ ((b - g) + (c - g))) a else 0 :=
  sourceQuadraticSmallResidue_eq_halfCoefficient F S₀ hζ g ((b - g) + (c - g))
    (sourceQuadraticPair_common_coprime_conductor F S₀ hζ b c g hb hc hg hclass) hM H

/-- The resulting common-pair residue difference is exactly the masked cutoff boundary sum. -/
theorem sourceQuadraticCommonPair_residueDifference (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (M H : ℝ) :
    sourceQuadraticSmallResidueFactor F M *
        quadraticHeckeCoprimeDensity F (Bad * C ((b - g) + (c - g))) *
      ((∑ a ∈ quadraticHeckeSquarefreeCutoff F H,
          if IsCoprime a Bad then quadraticHeckeHalfCoefficient F (Ψ ((b - g) + (c - g))) a else 0) *
          (∑ d ∈ HeckeIdealMobius.divisors F (I g), (UniqueFactorizationMonoid.moebius d : ℂ) *
            quadraticHeckeHalfCoefficient F (Ψ ((b - g) + (c - g))) d) -
        (∑ a ∈ quadraticHeckeCoprimeCutoff F (I g) H,
          if IsCoprime a Bad then quadraticHeckeHalfCoefficient F (Ψ ((b - g) + (c - g))) a else 0) *
          quadraticHeckeCoprimeDensity F (I g)) =
    sourceQuadraticSmallResidueFactor F M *
        quadraticHeckeCoprimeDensity F (Bad * C ((b - g) + (c - g))) *
      ∑ B ∈ quadraticHeckeCutoffAnnulus F (I g) H,
        if IsCoprime B Bad then quadraticHeckeCutoffCoefficient F (I g) H B *
          quadraticHeckeHalfCoefficient F (Ψ ((b - g) + (c - g))) B else 0 := by
  have hgs : sourceReflectionIsSquarefree g := by
    intro P
    have hgb : g ≤ b := hg ▸ (inf_le_left : b ⊓ c ≤ b)
    exact (hgb P).trans (hb P)
  have hχ (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥)
      (hJC : IsCoprime J (C ((b - g) + (c - g)))) :
      (Ψ ((b - g) + (c - g))).allCoefficient J ^ 2 = 1 := by
    unfold EvenIdealRayCharacter.allCoefficient
    rw [dite_eq_left hJ, ite_eq_left hJC]
    exact congrArg Units.val (sourceQuadraticRayCharacter_sq F S₀ hζ ((b - g) + (c - g)) _)
  have hcut := quadraticHeckeMainTerm_maskedCutoffGrouped F
    (Ψ ((b - g) + (c - g))) hχ (I g) Bad
    ((sourceReflectionExteriorIdeal_squarefree F S₀ g).mpr hgs)
    (sourceQuadraticPair_common_coprime_conductor F S₀ hζ b c g hb hc hg hclass)
    (sourceQuadraticBlock_exterior_coprime F S₀ g) H
  exact congrArg (fun z : ℂ => sourceQuadraticSmallResidueFactor F M *
    quadraticHeckeCoprimeDensity F (Bad * C ((b - g) + (c - g))) * z) hcut

end
end ArtinMatthews.SourceEulerAssembly
