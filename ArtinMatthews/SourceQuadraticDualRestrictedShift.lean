module

public import ArtinMatthews.SourceQuadraticDualRestrictedContour


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticDualRestrictedContour_line_independent (rows cols : Finset E)
    (u : E → ℂ) (g d : E) {X B σ τ : ℝ} (hX : 0 < X) (hB : 0 < B)
    (hσ : 0 < σ) (hσ₁ : σ < 1) (hτ : 0 < τ) (hτ₁ : τ < 1) :
    sourceQuadraticDualRestrictedContour F S₀ hζ rows cols u g d X B σ =
      sourceQuadraticDualRestrictedContour F S₀ hζ rows cols u g d X B τ := by
  unfold sourceQuadraticDualRestrictedContour
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [quadraticDualContourRemainder_line_independent F _
    (sourceQuadraticConductor_ne_bot F S₀ hζ _)
    (quadraticHeckeFieldScale F) (InfinitePlace.nrComplexPlaces F) sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
    sourceQuadraticBlockProfile_smooth hσ hσ₁ hτ hτ₁
    (Real.sqrt_pos.mpr (div_pos (sourceQuadraticDual_conductorNorm_pos F S₀ hζ _)
      (mul_pos hX (mul_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ a)) hB))))]

theorem sourceQuadraticDualRestrictedContour_rows_split (rows cols : Finset E)
    (u : E → ℂ) (g d : E) (X B σ T : ℝ) :
    sourceQuadraticDualRestrictedContour F S₀ hζ rows cols u g d X B σ =
      sourceQuadraticDualRestrictedContour F S₀ hζ
        (rows.filter (fun a => (q a : ℝ) ≤ T)) cols u g d X B σ +
      sourceQuadraticDualRestrictedContour F S₀ hζ
        (rows.filter (fun a => ¬ (q a : ℝ) ≤ T)) cols u g d X B σ := by
  unfold sourceQuadraticDualRestrictedContour
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← mul_add]
  congr 1
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem sourceQuadraticDualRestrictedContour_two_lines (rows cols : Finset E)
    (u : E → ℂ) (g d : E) {X B σ τ : ℝ} (hX : 0 < X) (hB : 0 < B)
    (hσ : 0 < σ) (hσ₁ : σ < 1) (hτ : 0 < τ) (hτ₁ : τ < 1) (T : ℝ) :
    sourceQuadraticDualRestrictedContour F S₀ hζ rows cols u g d X B σ =
      sourceQuadraticDualRestrictedContour F S₀ hζ
        (rows.filter (fun a => (q a : ℝ) ≤ T)) cols u g d X B σ +
      sourceQuadraticDualRestrictedContour F S₀ hζ
        (rows.filter (fun a => ¬ (q a : ℝ) ≤ T)) cols u g d X B τ := by
  rw [sourceQuadraticDualRestrictedContour_rows_split F S₀ hζ rows cols u g d X B σ T,
    sourceQuadraticDualRestrictedContour_line_independent F S₀ hζ
      (rows.filter (fun a => ¬ (q a : ℝ) ≤ T)) cols u g d
      hX hB hσ hσ₁ hτ hτ₁]

end
end ArtinMatthews.SourceEulerAssembly
