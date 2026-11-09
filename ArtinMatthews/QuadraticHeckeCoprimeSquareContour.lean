module

public import ArtinMatthews.QuadraticHeckeCoprimeContourRemainder
public import ArtinMatthews.QuadraticHeckeCoprimeNormReindex
public import ArtinMatthews.QuadraticHeckeCompactNormSummability


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory VaryingKummerAnalytic SourcePhysical
  UniqueFactorizationMonoid
open OAI.SevenEighths.ProbePhysical
open scoped NumberField ContDiff Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The original compact square-norm sum with the literal coprimality condition. -/
theorem quadraticHeckeCoprimeSquareNormContour_shift
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ X : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      if IsCoprime J.val m then w (((Ideal.absNorm J.val : ℝ) / X) ^ 2) else 0) =
      quadraticHeckeCoprimeContourRemainder F m
        (quadraticHeckeSquareMellin (mellin w)) σ X +
      (dedekindZeta_residue F : ℂ) * (X : ℂ) * ((1 / 2 : ℂ) * mellin w (1 / 2)) *
        quadraticHeckeCoprimeDensity F m := by
  rw [quadraticHeckeCoprimeNorm_reindex F m hm (fun t : ℝ => w (t ^ 2)) hX
    (quadraticHeckeCompactSquareNorm_summable F w hc hs.continuous hX)]
  calc
    _ = ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) *
        (verticalIntegral σ (fun s : ℂ =>
          (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ s) *
            quadraticHeckeSquareMellin (mellin w) s * mixedDedekindZeta F s) +
          (dedekindZeta_residue F : ℂ) * ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
            ((1 / 2 : ℂ) * mellin w (1 / 2))) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact congrArg (fun z : ℂ => (moebius d : ℂ) * z)
        (quadraticHeckeSquareNormContour_shift F w hc hp hs hσ₀ hσ₁
          (div_pos hX (quadraticHeckeCoprime_divisor_norm_pos F m hm hd)))
    _ = _ := quadraticHeckeCoprimeContour_residue F m hm
      (quadraticHeckeSquareMellin (mellin w)) σ X
      (dedekindZeta_residue F : ℂ) ((1 / 2 : ℂ) * mellin w (1 / 2))

end
end ArtinMatthews
