module

public import ArtinMatthews.QuadraticHeckeCoprimeSquareContour
public import ArtinMatthews.QuadraticHeckeDualSquareContour


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory VaryingKummerAnalytic SourcePhysical
  UniqueFactorizationMonoid
open OAI.SevenEighths.ProbePhysical
open scoped NumberField ContDiff Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The Mellin-dual square-norm sum has the same exact coprime residue density. -/
theorem quadraticHeckeCoprimeDualSquareNormContour_shift
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ X : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      if IsCoprime J.val m then
        quadraticHeckeDualProfile A r w (((Ideal.absNorm J.val : ℝ) / X) ^ 2) else 0) =
      quadraticHeckeCoprimeContourRemainder F m
        (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) σ X +
      (dedekindZeta_residue F : ℂ) * (X : ℂ) * ((1 / 2 : ℂ) * mellin w (1 / 2)) *
        quadraticHeckeCoprimeDensity F m := by
  rw [quadraticHeckeCoprimeNorm_reindex F m hm
    (fun t : ℝ => quadraticHeckeDualProfile A r w (t ^ 2)) hX
    (quadraticHeckeDualSquareNorm_summable F A r w hc hp hs hX)]
  calc
    _ = ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) *
        (verticalIntegral σ (fun s : ℂ =>
          (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ s) *
            quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w) s *
              mixedDedekindZeta F s) +
          (dedekindZeta_residue F : ℂ) * ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
            ((1 / 2 : ℂ) * mellin w (1 / 2))) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact congrArg (fun z : ℂ => (moebius d : ℂ) * z)
        (quadraticHeckeDualSquareNormContour_shift F A r w hc hp hs hσ₀ hσ₁
          (div_pos hX (quadraticHeckeCoprime_divisor_norm_pos F m hm hd)))
    _ = _ := quadraticHeckeCoprimeContour_residue F m hm
      (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) σ X
      (dedekindZeta_residue F : ℂ) ((1 / 2 : ℂ) * mellin w (1 / 2))

/-- At the same norm scale the original and dual residues cancel exactly. -/
theorem quadraticHeckeCoprimeSquareNormContour_sub_dual
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ X : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      if IsCoprime J.val m then w (((Ideal.absNorm J.val : ℝ) / X) ^ 2) else 0) -
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      if IsCoprime J.val m then
        quadraticHeckeDualProfile A r w (((Ideal.absNorm J.val : ℝ) / X) ^ 2) else 0) =
      quadraticHeckeCoprimeContourRemainder F m
        (quadraticHeckeSquareMellin (mellin w)) σ X -
      quadraticHeckeCoprimeContourRemainder F m
        (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) σ X := by
  rw [quadraticHeckeCoprimeSquareNormContour_shift F m hm w hc hp hs hσ₀ hσ₁ hX,
    quadraticHeckeCoprimeDualSquareNormContour_shift F m hm A r w hc hp hs hσ₀ hσ₁ hX]
  ring

end
end ArtinMatthews
