module

public import ArtinMatthews.SourceQuadraticSmallContourIntegral
public import ArtinMatthews.SourceQuadraticPoissonErrorKernels
public import ArtinMatthews.SourceQuadraticPoissonErrorSeparation
public import ArtinMatthews.SourceQuadraticBlockDivisorExpansion


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex MeasureTheory Set VaryingKummerAnalytic
open OAI.SevenEighths.ProbePhysical
open UniqueFactorizationMonoid
open scoped NumberField Classical ContDiff BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]

def quadraticDualContourKernel (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (σ t : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * quadraticHeckeDualSquareErrorKernel F A r w σ t

theorem quadraticDualContourKernel_continuous (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≠ 1) : Continuous (quadraticDualContourKernel F A r w σ) :=
  (quadraticHeckeDualSquareErrorKernel_continuous F A r w hc hp hs hσ hσone).const_mul _

theorem quadraticDualContourKernel_integrable (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ : ℝ} (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1) :
    Integrable (quadraticDualContourKernel F A r w σ) :=
  (quadraticHeckeDualSquareErrorKernel_integrable F A r w hc hp hs hσ hσtop hσone).const_mul _

theorem quadraticDualContourRemainder_eq_integral
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ X : ℝ} (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1) (hX : 0 < X) :
    quadraticHeckeCoprimeContourRemainder F m (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) σ X =
      ∫ t : ℝ, quadraticDualContourKernel F A r w σ t *
        (X : ℂ) ^ quadraticPoissonLine σ t * quadraticSmallEuler F m (quadraticPoissonLine σ t) := by
  let H := quadraticHeckeDualSquareErrorKernel F A r w σ
  have hHc := quadraticHeckeDualSquareErrorKernel_continuous F A r w hc hp hs hσ hσone
  have hHi := quadraticHeckeDualSquareErrorKernel_integrable F A r w hc hp hs hσ hσtop hσone
  have hx (d : Ideal (𝓞 F)) (hd : d ∈ HeckeIdealMobius.divisors F m) :
      0 < X / (Ideal.absNorm d : ℝ) :=
    div_pos hX (quadraticHeckeCoprime_divisor_norm_pos F m hm hd)
  have hsum := quadraticPoissonLine_finite_sum (HeckeIdealMobius.divisors F m) H hHc hHi σ
    (fun d => X / (Ideal.absNorm d : ℝ)) hx (fun d => (moebius d : ℂ))
  have hterm (d : Ideal (𝓞 F)) :
      verticalIntegral σ (fun s : ℂ =>
        ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ s *
          quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w) s * mixedDedekindZeta F s) =
        (1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, H t * ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ quadraticPoissonLine σ t := by
    unfold verticalIntegral
    push_cast
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    dsimp [H, quadraticHeckeDualSquareErrorKernel, quadraticHeckeHalfZetaKernel,
      quadraticHeckeSquareMellin, quadraticPoissonLine]
    ring
  unfold quadraticHeckeCoprimeContourRemainder
  simp_rw [hterm]
  calc
    _ = (1 / (2 * Real.pi) : ℂ) * ∑ d ∈ HeckeIdealMobius.divisors F m,
        (moebius d : ℂ) * ∫ t : ℝ, H t *
          ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ quadraticPoissonLine σ t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, H t *
        ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) *
          ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ quadraticPoissonLine σ t := by rw [hsum]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [quadraticSmallEuler_scaled_sum F m hm hX (quadraticPoissonLine σ t) (by
        intro hz
        have hre := congrArg Complex.re hz
        simp only [quadraticPoissonLine_re, zero_re] at hre
        exact hσ.ne' hre)]
      dsimp only [H, quadraticDualContourKernel]
      ring

end
end ArtinMatthews
