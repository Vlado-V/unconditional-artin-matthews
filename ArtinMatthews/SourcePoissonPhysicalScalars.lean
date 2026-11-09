module

public import ArtinMatthews.SourcePoissonOriginalProbe


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

/-- The exact index, dilation and finite Fourier factors in physical Poisson. -/
theorem sourcePoissonPhysicalDilationFactor {X qs qA : ℝ}
    (hX : 0 < X) (hs : 0 < qs) (hA : 0 < qA) :
    (Real.sqrt (qs * X))⁻¹ * ((qs * X) / (qs * qA)) * Real.sqrt qs =
      Real.sqrt X / qA := by
  have hs' := (Real.sqrt_pos.mpr hs).ne'
  have hX' := (Real.sqrt_pos.mpr hX).ne'
  rw [Real.sqrt_mul hs.le]
  field_simp [hs.ne', hA.ne', hs', hX']
  exact (Real.sq_sqrt hX.le).symm

theorem sourcePoissonPhysicalDilationFactor_complex {X qs qA : ℝ}
    (hX : 0 < X) (hs : 0 < qs) (hA : 0 < qA) :
    (Real.sqrt (qs * X) : ℂ)⁻¹ * (((qs * X) / (qs * qA) : ℝ) : ℂ) *
      (Real.sqrt qs : ℂ) = ((Real.sqrt X / qA : ℝ) : ℂ) := by
  exact_mod_cast sourcePoissonPhysicalDilationFactor hX hs hA

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

/-- The Gaussian factor independent of the original lattice point. -/
def sourcePoissonPhysicalGaussianCoefficient
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (c : ReflectionSquarefreeExponents F S₀) (n : SourcePrimeExponents F S₀)
    (Z : ℝ) : ℂ :=
  let A := c.val + 3 • n
  reflectionGammaTwo F hζ S₀ c.val /
      ((Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) : ℂ) *
        (sourcePrimeExponentNorm F S₀ n : ℂ)) *
    reflectionThetaValue F hζ S₀ hBad η A *
    (reflectionGaussian ((sourcePrimeExponentNorm F S₀ A : ℝ) / Z) : ℂ)

theorem sourcePoissonPhysicalGaussianCoefficient_mul_residue
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (c : ReflectionSquarefreeExponents F S₀) (n : SourcePrimeExponents F S₀)
    (m : sourceRing F S₀) (Z : ℝ) :
    sourcePoissonPhysicalGaussianCoefficient F S₀ hζ η hBad c n Z *
      reflectionExponentResidueValue F hζ S₀ (c.val + 3 • n) m =
    reflectionCoefficientTerm F hζ S₀ hBad η c n m Z := by
  unfold sourcePoissonPhysicalGaussianCoefficient reflectionCoefficientTerm
  dsimp only
  ac_rfl

end
end ArtinMatthews.SourceEulerAssembly
