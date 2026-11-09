module

public import ArtinMatthews.SourceQuadraticB3SignedAssembly
public import ArtinMatthews.SourceQuadraticDiagonalResidue


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical
noncomputable section

private theorem signed_re_le_norms (d e t s r : ℂ) :
    (d + e + t - s + r).re ≤ ‖d‖ + ‖e‖ + ‖t‖ + ‖s‖ + ‖r‖ := by
  have hs : -s.re ≤ ‖s‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  simp only [Complex.add_re, Complex.sub_re]
  linarith [Complex.re_le_norm d, Complex.re_le_norm e, Complex.re_le_norm t,
    Complex.re_le_norm r]

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticB3Block_re_le_component_norms {M K σ τ : ℝ}
    (hM : 0 < M) (hK : 0 ≤ K) (hσ : 0 < σ) (hσone : σ < 1)
    (hτ : 0 < τ) (hτone : τ < 1)
    (cols : Finset E) (u : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) :
    (sourceQuadraticB3Block F S₀ hζ (sourceQuadraticB2Rows F S₀ M K) cols
        (sourceQuadraticB2RowWeight F S₀ M) u g).re ≤
      ‖sourceQuadraticZeroResidualBlock F S₀
          (sourceQuadraticBlockIdealFull F S₀ hζ M g) cols u g‖ +
        ‖sourceQuadraticNonzeroResidualBlock F S₀
          (sourceQuadraticDualDivisorError F S₀ hζ M K τ g) cols u g‖ +
        ‖sourceQuadraticNonzeroResidualBlock F S₀
          (sourceQuadraticDualDivisorTail F S₀ hζ M K g) cols u g‖ +
        ‖sourceQuadraticOriginalSmallErrorBlock F S₀ hζ M K σ cols u g‖ +
        ‖sourceQuadraticCommonPairBlock F S₀ (fun e =>
          sourceQuadraticDualDivisorResidue F S₀ hζ M K g e -
          sourceQuadraticOriginalSmallResidue F S₀ hζ M K g e) cols u g‖ := by
  rw [sourceQuadraticB3Block_signed_components F S₀ hζ hM hK hσ hσone hτ hτone cols u g hcols]
  exact (sourceQuadratic_sub_fullResidueDiagonal_re_le F S₀ hζ hM K cols u g _).trans
    (signed_re_le_norms _ _ _ _ _)

end
end ArtinMatthews.SourceEulerAssembly
