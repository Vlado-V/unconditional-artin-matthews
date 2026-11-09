module

public import ArtinMatthews.SourceQuadraticNormalizedResidue


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic VaryingKummerAnalytic QuadraticScale
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

omit [IsTotallyComplex F] in
private theorem residueFactor_sqrt (M : ℝ) :
    sourceQuadraticSmallResidueFactor F M =
      sourceQuadraticSmallResidueFactor F 1 * (Real.sqrt M : ℂ) := by
  unfold sourceQuadraticSmallResidueFactor
  rw [Real.sqrt_one, Complex.ofReal_one]
  ring

/-- The signed residue difference is bounded after the exact common-pair cancellation. -/
theorem sourceQuadraticNormalizedResidueBlock_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cBound : ℝ, 0 < cBound ∧ ∀ M P H : ℝ, 1 ≤ M → 1 ≤ P → 1 ≤ H → H ≤ M →
      ∀ (cols : Finset E) (u : E → ℂ) (g : E),
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ P) →
      (∀ b ∈ cols, ∀ c ∈ cols, b ⊓ c = g →
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ‖sourceQuadraticNormalizedResidueBlock F S₀ hζ M H cols u g‖ ≤
        cBound * (q g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ cols, ‖u b‖ ^ 2 := by
  obtain ⟨cBound, hc, hbound⟩ :=
    sourceQuadraticBlockRadical_canonicalMain_bound F S₀ hζ htrace hE ε hε
  refine ⟨(‖sourceQuadraticSmallResidueFactor F 1‖ + 1) * cBound, by positivity, ?_⟩
  intro M P H hM hP hH hHM cols u g hcols hclass
  rw [sourceQuadraticNormalizedResidueBlock_eq_main F S₀ hζ M H cols u g
    (fun b hb => (hcols b hb).1) hclass, residueFactor_sqrt, mul_assoc, norm_mul]
  have hresSF := sourceQuadraticSmallResidualColumns_squarefree F S₀ cols g
    (fun b hb => (hcols b hb).1)
  have hresNorm := sourceQuadraticSmallResidualColumns_norm F S₀ cols g P
    (fun b hb => (hcols b hb).2)
  have hb := hbound M P H hM hP hH hHM g
    (sourceQuadraticSmallResidualColumns F S₀ cols g)
    (fun b hmem => ⟨hresSF b hmem, hresNorm b hmem⟩)
    (sourceQuadraticSmallResidualCoeff F S₀ g (sourceQuadraticDensityTwistedCoeff F S₀ g u))
  have hmass :
      (∑ b ∈ sourceQuadraticSmallResidualColumns F S₀ cols g,
        ‖sourceQuadraticSmallResidualCoeff F S₀ g (sourceQuadraticDensityTwistedCoeff F S₀ g u) b‖ ^ 2) ≤
      ∑ b ∈ cols, ‖u b‖ ^ 2 :=
    (sourceQuadraticSmallResidualCoeff_mass F S₀ cols g
      (sourceQuadraticDensityTwistedCoeff F S₀ g u)).trans
      (sourceQuadraticDensityTwistedCoeff_mass F S₀ cols g u)
  calc
    _ ≤ ‖sourceQuadraticSmallResidueFactor F 1‖ *
        (cBound * (q g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ sourceQuadraticSmallResidualColumns F S₀ cols g,
              ‖sourceQuadraticSmallResidualCoeff F S₀ g (sourceQuadraticDensityTwistedCoeff F S₀ g u) b‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ (‖sourceQuadraticSmallResidueFactor F 1‖ + 1) *
        (cBound * (q g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ cols, ‖u b‖ ^ 2) := by gcongr; exact le_add_of_nonneg_right zero_le_one
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
