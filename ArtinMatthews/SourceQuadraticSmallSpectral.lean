module

public import ArtinMatthews.SourceQuadraticSmallIntegrand
public import ArtinMatthews.SourceQuadraticSmallAmplitude


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ

/-- A finite, absolutely integrable expression for one Small contour error. -/
def sourceQuadraticSmallErrorIntegrand (M K σ : ℝ) (g e : E) (t : ℝ) : ℂ :=
  ∑ a ∈ sourceQuadraticSmallRows F S₀ K g,
    (Ψ e).allCoefficient (I a) *
      (quadraticSmallContourKernel F sourceQuadraticBlockProfile σ t *
        (Real.sqrt (M / (q a : ℝ)) : ℂ) ^ quadraticPoissonLine σ t *
        quadraticSmallEuler F (sourceQuadraticBlockSquareModulus F S₀ hζ g e)
          (quadraticPoissonLine σ t))

theorem sourceQuadraticSmallErrorIntegrand_integrable {M K σ : ℝ}
    (hM : 0 < M) (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1) (g e : E) :
    Integrable (sourceQuadraticSmallErrorIntegrand F S₀ hζ M K σ g e) := by
  apply integrable_finsetSum
  intro a _
  have hq : 0 < (q a : ℝ) := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a)
  exact (quadraticSmallContourIntegrand_integrable F
    (sourceQuadraticBlockSquareModulus F S₀ hζ g e) sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
    sourceQuadraticBlockProfile_smooth hσ hσtop hσone (Real.sqrt_pos.mpr (div_pos hM hq))).const_mul _

theorem sourceQuadraticOriginalSmallError_eq_integral {M K σ : ℝ}
    (hM : 0 < M) (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1) (g e : E) :
    sourceQuadraticOriginalSmallError F S₀ hζ M K σ g e =
      ∫ t : ℝ, sourceQuadraticSmallErrorIntegrand F S₀ hζ M K σ g e t := by
  unfold sourceQuadraticOriginalSmallError sourceQuadraticSmallErrorIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_const_mul, quadraticSmallContourRemainder_eq_integral F
      (sourceQuadraticBlockSquareModulus F S₀ hζ g e)
      (sourceQuadraticBlockSquareModulus_ne_bot F S₀ hζ g e)
      sourceQuadraticBlockProfile sourceQuadraticBlockProfile_compact
      sourceQuadraticBlockProfile_positive sourceQuadraticBlockProfile_smooth hσ hσtop hσone]
    exact Real.sqrt_pos.mpr (div_pos hM (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a)))
  · intro a _
    exact (quadraticSmallContourIntegrand_integrable F
      (sourceQuadraticBlockSquareModulus F S₀ hζ g e) sourceQuadraticBlockProfile
      sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
      sourceQuadraticBlockProfile_smooth hσ hσtop hσone
      (Real.sqrt_pos.mpr (div_pos hM (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a))))).const_mul _

theorem sourceQuadraticSmallSpectralIntegrand_eq {M : ℝ} (hM : 0 < M)
    (K σ : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) (t : ℝ) :
    (∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
      star (u p.1) * u p.2 *
        sourceQuadraticSmallErrorIntegrand F S₀ hζ M K σ g ((p.1 - g) + (p.2 - g)) t) =
      quadraticSmallContourKernel F sourceQuadraticBlockProfile σ t *
        (M : ℂ) ^ (quadraticPoissonLine σ t / 2) *
        sourceQuadraticOriginalSmallAmplitude F S₀ hζ K cols u g (quadraticPoissonLine σ t) := by
  unfold sourceQuadraticSmallErrorIntegrand sourceQuadraticOriginalSmallAmplitude
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro a _
  rw [quadraticSmall_sqrt_ratio_cpow hM (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a))]
  push_cast
  ring

theorem sourceQuadraticOriginalSmallErrorBlock_eq_integral {M K σ : ℝ}
    (hM : 0 < M) (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1)
    (cols : Finset E) (u : E → ℂ) (g : E) :
    sourceQuadraticOriginalSmallErrorBlock F S₀ hζ M K σ cols u g =
      ∫ t : ℝ, quadraticSmallContourKernel F sourceQuadraticBlockProfile σ t *
        (M : ℂ) ^ (quadraticPoissonLine σ t / 2) *
        sourceQuadraticOriginalSmallAmplitude F S₀ hζ K cols u g (quadraticPoissonLine σ t) := by
  unfold sourceQuadraticOriginalSmallErrorBlock
  simp_rw [sourceQuadraticOriginalSmallError_eq_integral F S₀ hζ hM hσ hσtop hσone]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · exact integral_congr_ae (ae_of_all _ (sourceQuadraticSmallSpectralIntegrand_eq F S₀ hζ hM K σ cols u g))
  · intro p _
    exact (sourceQuadraticSmallErrorIntegrand_integrable F S₀ hζ hM hσ hσtop hσone g _).const_mul _

theorem sourceQuadraticOriginalSmallErrorBlock_integrable {M K σ : ℝ}
    (hM : 0 < M) (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1)
    (cols : Finset E) (u : E → ℂ) (g : E) :
    Integrable (fun t : ℝ => quadraticSmallContourKernel F sourceQuadraticBlockProfile σ t *
      (M : ℂ) ^ (quadraticPoissonLine σ t / 2) *
      sourceQuadraticOriginalSmallAmplitude F S₀ hζ K cols u g (quadraticPoissonLine σ t)) := by
  have hi : Integrable (fun t : ℝ =>
      ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
        star (u p.1) * u p.2 * sourceQuadraticSmallErrorIntegrand F S₀ hζ M K σ g
          ((p.1 - g) + (p.2 - g)) t) := by
    apply integrable_finsetSum
    intro p _
    exact (sourceQuadraticSmallErrorIntegrand_integrable F S₀ hζ hM hσ hσtop hσone g _).const_mul _
  exact hi.congr (ae_of_all _ (sourceQuadraticSmallSpectralIntegrand_eq F S₀ hζ hM K σ cols u g))

end
end ArtinMatthews.SourceEulerAssembly
