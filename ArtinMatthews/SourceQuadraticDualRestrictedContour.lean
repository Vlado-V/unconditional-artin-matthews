module

public import ArtinMatthews.SourceQuadraticDualFiniteErrors
public import ArtinMatthews.SourceQuadraticDualIntegrand
public import ArtinMatthews.SourceQuadraticDualPairAmplitude


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Complex
noncomputable section

theorem quadraticDual_bad_scale_cpow {X Q N B : ℝ}
    (hX : 0 < X) (hQ : 0 < Q) (hN : 0 < N) (hB : 0 < B) (s : ℂ) :
    (Real.sqrt (Q / (X * (N * B))) : ℂ) ^ s =
      (B : ℂ) ^ (-(s/2)) * (Real.sqrt (Q / (X*N)) : ℂ) ^ s := by
  rw [quadraticDual_sqrt_ratio_cpow hX hQ (mul_pos hN hB),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hN.le hB.le,
    quadraticDual_sqrt_ratio_cpow hX hQ hN]
  ring

end
end ArtinMatthews

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "C" e:max => sourceQuadraticConductor F S₀ hζ e
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ
local notation "A" => quadraticHeckeFieldScale F
local notation "r" => InfinitePlace.nrComplexPlaces F

def sourceQuadraticDualRestrictedContour (rows cols : Finset E) (u : E → ℂ)
    (g d : E) (X B σ : ℝ) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    star (u p.1) * u p.2 * χ d ((p.1-g)+(p.2-g)) *
      ((X / Real.sqrt (Ideal.absNorm (C ((p.1-g)+(p.2-g))))) : ℝ) *
      ∑ a ∈ rows, (Ψ ((p.1-g)+(p.2-g))).allCoefficient (I a) *
        quadraticHeckeCoprimeContourRemainder F (C ((p.1-g)+(p.2-g)))
          (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r sourceQuadraticBlockProfile))
          σ (Real.sqrt ((Ideal.absNorm (C ((p.1-g)+(p.2-g))) : ℝ) /
            (X*((q a : ℝ)*B))))

def sourceQuadraticDualRestrictedIntegrand (rows cols : Finset E) (u : E → ℂ)
    (g d : E) (X B σ t : ℝ) : ℂ :=
  quadraticDualContourKernel F A r sourceQuadraticBlockProfile σ t *
    (B : ℂ)^(-(quadraticPoissonLine σ t/2)) *
      sourceQuadraticDualPairAmplitude F S₀ hζ rows cols u g d X (quadraticPoissonLine σ t)

private def expandedIntegrand (rows cols : Finset E) (u : E → ℂ)
    (g d : E) (X B σ t : ℝ) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    star (u p.1) * u p.2 * χ d ((p.1-g)+(p.2-g)) *
      ((X / Real.sqrt (Ideal.absNorm (C ((p.1-g)+(p.2-g))))) : ℝ) *
      ∑ a ∈ rows, (Ψ ((p.1-g)+(p.2-g))).allCoefficient (I a) *
        (quadraticDualContourKernel F A r sourceQuadraticBlockProfile σ t *
          (Real.sqrt ((Ideal.absNorm (C ((p.1-g)+(p.2-g))) : ℝ) /
            (X*((q a : ℝ)*B))) : ℂ)^(quadraticPoissonLine σ t) *
          quadraticSmallEuler F (C ((p.1-g)+(p.2-g))) (quadraticPoissonLine σ t))

private theorem expanded_integrable (rows cols : Finset E) (u : E → ℂ)
    (g d : E) {X B σ : ℝ} (hX : 0 < X) (hB : 0 < B)
    (hσ : 0 < σ) (hσtop : σ ≤ 5/4) (hσone : σ ≠ 1) :
    Integrable (expandedIntegrand F S₀ hζ rows cols u g d X B σ) := by
  apply integrable_finsetSum
  intro p _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro a _
  exact (quadraticDualContourIntegrand_integrable F _ A r sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
    sourceQuadraticBlockProfile_smooth hσ hσtop hσone
    (Real.sqrt_pos.mpr (div_pos (sourceQuadraticDual_conductorNorm_pos F S₀ hζ _)
      (mul_pos hX (mul_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a)) hB))))).const_mul _

private theorem expanded_eq (rows cols : Finset E) (u : E → ℂ)
    (g d : E) {X B : ℝ} (hX : 0 < X) (hB : 0 < B) (σ t : ℝ) :
    expandedIntegrand F S₀ hζ rows cols u g d X B σ t =
      sourceQuadraticDualRestrictedIntegrand F S₀ hζ rows cols u g d X B σ t := by
  unfold expandedIntegrand sourceQuadraticDualRestrictedIntegrand sourceQuadraticDualPairAmplitude
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro a _
  rw [quadraticDual_bad_scale_cpow hX (sourceQuadraticDual_conductorNorm_pos F S₀ hζ _)
    (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a)) hB]
  push_cast
  ring

theorem sourceQuadraticDualRestrictedIntegrand_integrable (rows cols : Finset E)
    (u : E → ℂ) (g d : E) {X B σ : ℝ} (hX : 0 < X) (hB : 0 < B)
    (hσ : 0 < σ) (hσtop : σ ≤ 5/4) (hσone : σ ≠ 1) :
    Integrable (sourceQuadraticDualRestrictedIntegrand F S₀ hζ rows cols u g d X B σ) :=
  (expanded_integrable F S₀ hζ rows cols u g d hX hB hσ hσtop hσone).congr
    (ae_of_all _ (expanded_eq F S₀ hζ rows cols u g d hX hB σ))

theorem sourceQuadraticDualRestrictedContour_eq_integral (rows cols : Finset E)
    (u : E → ℂ) (g d : E) {X B σ : ℝ} (hX : 0 < X) (hB : 0 < B)
    (hσ : 0 < σ) (hσtop : σ ≤ 5/4) (hσone : σ ≠ 1) :
    sourceQuadraticDualRestrictedContour F S₀ hζ rows cols u g d X B σ =
      ∫ t : ℝ, sourceQuadraticDualRestrictedIntegrand F S₀ hζ rows cols u g d X B σ t := by
  rw [← integral_congr_ae (ae_of_all _ (expanded_eq F S₀ hζ rows cols u g d hX hB σ))]
  unfold expandedIntegrand sourceQuadraticDualRestrictedContour
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_const_mul, integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_const_mul, quadraticDualContourRemainder_eq_integral F _
        (sourceQuadraticConductor_ne_bot F S₀ hζ _) A r sourceQuadraticBlockProfile
        sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
        sourceQuadraticBlockProfile_smooth hσ hσtop hσone
        (Real.sqrt_pos.mpr (div_pos (sourceQuadraticDual_conductorNorm_pos F S₀ hζ _)
          (mul_pos hX (mul_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a)) hB))))]
    · intro a _
      exact (quadraticDualContourIntegrand_integrable F _ A r sourceQuadraticBlockProfile
        sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
        sourceQuadraticBlockProfile_smooth hσ hσtop hσone
        (Real.sqrt_pos.mpr (div_pos (sourceQuadraticDual_conductorNorm_pos F S₀ hζ _)
          (mul_pos hX (mul_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a)) hB))))).const_mul _
  · intro p _
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro a _
    exact (quadraticDualContourIntegrand_integrable F _ A r sourceQuadraticBlockProfile
      sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
      sourceQuadraticBlockProfile_smooth hσ hσtop hσone
      (Real.sqrt_pos.mpr (div_pos (sourceQuadraticDual_conductorNorm_pos F S₀ hζ _)
        (mul_pos hX (mul_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a)) hB))))).const_mul _

end
end ArtinMatthews.SourceEulerAssembly
