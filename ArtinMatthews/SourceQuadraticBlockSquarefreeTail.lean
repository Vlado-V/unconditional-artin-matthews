module

public import ArtinMatthews.SourceQuadraticDualSquarefreeTailBound
public import ArtinMatthews.SourceQuadraticBlockDualCutoff
public import ArtinMatthews.SourceQuadraticDualSquarefreeContour


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

/-- The actual exterior divisor tail, including the Möbius, character and Poisson factors. -/
def sourceQuadraticBlockSquarefreeTail (M : ℝ) (g e : E) (K : ℝ) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
    sourceQuadraticBlockDualPrefactor F S₀ hζ M e d *
      sourceQuadraticDualSquarefreeTail F S₀ hζ e (M / (Ideal.absNorm d : ℝ)) K

/-- The existing divisor-contour formula splits into its literal finite part and this tail. -/
theorem sourceQuadraticBlockContours_split_tail (M σ : ℝ) (g e : E) (K : ℝ) :
    sourceQuadraticDualDivisorContours F S₀ hζ M σ g e (fun _ => K) =
      (∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
        sourceQuadraticBlockDualPrefactor F S₀ hζ M e d *
          sourceQuadraticDualSquarefreeContours F S₀ hζ e
            (M / (Ideal.absNorm d : ℝ)) K σ) +
      sourceQuadraticBlockSquarefreeTail F S₀ hζ M g e K := by
  simp only [sourceQuadraticDualDivisorContours, sourceQuadraticBlockSquarefreeTail,
    sourceQuadraticBlockDualPrefactor, mul_add, Finset.sum_add_distrib]

/-- Absolute source tails give the exact finite-divisor majorant. -/
theorem sourceQuadraticBlockSquarefreeTail_bound {u σ : ℝ}
    (hu : 1 < u) (huσ : u ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ), 0 < M → ∀ (g e : E) (K : ℝ), 0 < K →
      ‖sourceQuadraticBlockSquarefreeTail F S₀ hζ M g e K‖ ≤
        C * ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
          ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M e d‖ *
            sourceQuadraticBlockDualScale F S₀ hζ M e d ^ (-σ) * K ^ (u - σ) := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticDualSquarefreeTail_bound F S₀ hζ hu huσ
  refine ⟨C, hC, ?_⟩
  intro M hM g e K hK
  unfold sourceQuadraticBlockSquarefreeTail
  calc
    _ ≤ ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
        ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M e d *
          sourceQuadraticDualSquarefreeTail F S₀ hζ e (M / (Ideal.absNorm d : ℝ)) K‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ HeckeIdealMobius.divisors F (sourceQuadraticBlockModulus F S₀ g),
        ‖sourceQuadraticBlockDualPrefactor F S₀ hζ M e d‖ *
          (C * sourceQuadraticBlockDualScale F S₀ hζ M e d ^ (-σ) * K ^ (u - σ)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact hbound e (M / (Ideal.absNorm d : ℝ)) K
        (div_pos hM (sourceQuadraticBlock_divisorNorm_pos F S₀ g d hd)) hK
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring

end
end ArtinMatthews.SourceEulerAssembly
