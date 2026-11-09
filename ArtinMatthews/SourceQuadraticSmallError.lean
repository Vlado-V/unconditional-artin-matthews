module

public import ArtinMatthews.SourceQuadraticSmallRows
public import ArtinMatthews.SourceQuadraticBlockSmallContour
public import ArtinMatthews.SourceQuadraticSmallContourIntegral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Set MeasureTheory VaryingKummerAnalytic
open scoped NumberField Classical ContDiff BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ

/-- The original positive-line Small error, on its literal finite exterior rows. -/
def sourceQuadraticOriginalSmallError (M K σ : ℝ) (g e : E) : ℂ :=
  ∑ a ∈ sourceQuadraticSmallRows F S₀ K g,
    (Ψ e).allCoefficient (I a) *
      quadraticHeckeCoprimeContourRemainder F (sourceQuadraticBlockSquareModulus F S₀ hζ g e)
        (quadraticHeckeSquareMellin (mellin sourceQuadraticBlockProfile)) σ
        (Real.sqrt (M / (q a : ℝ)))

/-- The actual common-ideal contribution of the Small contour errors. -/
def sourceQuadraticOriginalSmallErrorBlock (M K σ : ℝ) (cols : Finset E)
    (u : E → ℂ) (g : E) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    star (u p.1) * u p.2 *
      sourceQuadraticOriginalSmallError F S₀ hζ M K σ g ((p.1 - g) + (p.2 - g))

theorem sourceQuadraticOriginalSmallError_eq_ideal_sum {K : ℝ} (hK : 0 ≤ K)
    (M σ : ℝ) (g e : E) :
    sourceQuadraticOriginalSmallError F S₀ hζ M K σ g e =
      ∑' a : {J : Ideal (𝓞 F) // Squarefree J},
        if IsCoprime a.val (sourceQuadraticBlockBadIdeal F S₀) ∧ IsCoprime a.val (I g) ∧
          (Ideal.absNorm a.val : ℝ) ≤ K then
          (Ψ e).allCoefficient a.val *
            quadraticHeckeCoprimeContourRemainder F
              (sourceQuadraticBlockSquareModulus F S₀ hζ g e)
              (quadraticHeckeSquareMellin (mellin sourceQuadraticBlockProfile)) σ
              (Real.sqrt (M / (Ideal.absNorm a.val : ℝ))) else 0 := by
  rw [sourceQuadraticSmallRows_tsum F S₀ hK g (fun J =>
    (Ψ e).allCoefficient J * quadraticHeckeCoprimeContourRemainder F
      (sourceQuadraticBlockSquareModulus F S₀ hζ g e)
      (quadraticHeckeSquareMellin (mellin sourceQuadraticBlockProfile)) σ
      (Real.sqrt (M / (Ideal.absNorm J : ℝ))))]
  simp only [sourceQuadraticOriginalSmallError, sourcePrimeExponentIdeal_norm]

/-- The residue retained by the exact Small decomposition. -/
def sourceQuadraticOriginalSmallResidue (M K : ℝ) (g e : E) : ℂ :=
  ∑ a ∈ sourceQuadraticSmallRows F S₀ K g,
    (Ψ e).allCoefficient (I a) *
      ((dedekindZeta_residue F : ℂ) * (Real.sqrt (M / (q a : ℝ)) : ℂ) *
        ((1 / 2 : ℂ) * mellin sourceQuadraticBlockProfile (1 / 2)) *
        quadraticHeckeCoprimeDensity F (sourceQuadraticBlockSquareModulus F S₀ hζ g e))

theorem sourceQuadraticBlockIdealSmall_eq_error_add_residue {M K σ : ℝ}
    (hM : 0 < M) (hK : 0 ≤ K) (hσ : 0 < σ) (hσone : σ < 1) (g e : E) :
    sourceQuadraticBlockIdealSmall F S₀ hζ M K g e =
      sourceQuadraticOriginalSmallError F S₀ hζ M K σ g e +
        sourceQuadraticOriginalSmallResidue F S₀ hζ M K g e := by
  rw [sourceQuadraticBlockIdealSmall_eq_contours F S₀ hζ hM hσ hσone]
  rw [sourceQuadraticSmallRows_tsum F S₀ hK g (fun J =>
    (Ψ e).allCoefficient J *
      (quadraticHeckeCoprimeContourRemainder F (sourceQuadraticBlockSquareModulus F S₀ hζ g e)
        (quadraticHeckeSquareMellin (mellin sourceQuadraticBlockProfile)) σ
        (Real.sqrt (M / (Ideal.absNorm J : ℝ))) +
      (dedekindZeta_residue F : ℂ) * (Real.sqrt (M / (Ideal.absNorm J : ℝ)) : ℂ) *
        ((1 / 2 : ℂ) * mellin sourceQuadraticBlockProfile (1 / 2)) *
        quadraticHeckeCoprimeDensity F (sourceQuadraticBlockSquareModulus F S₀ hζ g e)))]
  simp only [sourcePrimeExponentIdeal_norm, mul_add, Finset.sum_add_distrib,
    sourceQuadraticOriginalSmallError, sourceQuadraticOriginalSmallResidue]

end
end ArtinMatthews.SourceEulerAssembly
