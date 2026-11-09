module

public import ArtinMatthews.SourcePoissonPhysicalCauchy
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil
open MeasureTheory Filter Asymptotics
open scoped NumberField Classical BigOperators Topology
noncomputable section

theorem sourcePoissonPhysicalMoment_exponent
    {Z A B : ℝ} (hZ : 0 < Z) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A * Z ^ (-(133 / 1000) : ℝ)) *
      Real.sqrt (B * Z ^ (533 / 500 + 1 / 50000 : ℝ)) =
      (Real.sqrt A * Real.sqrt B) * Z ^ (933 / 2000 + 1 / 100000 : ℝ) := by
  have hp (r : ℝ) : Real.sqrt (Z ^ r) = Z ^ (r / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [Real.sqrt_mul hA, Real.sqrt_mul hB, hp, hp]
  calc
    _ = (Real.sqrt A * Real.sqrt B) *
        (Z ^ (-(133 / 1000) / 2 : ℝ) * Z ^ ((533 / 500 + 1 / 50000) / 2 : ℝ)) := by ac_rfl
    _ = _ := by
      rw [← Real.rpow_add hZ]
      norm_num

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "D" => sNormOneFundamentalSet F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v

/-- The literal two square-moment estimates imply the manuscript probe exponent.
The finite set may depend on the actual bounded representative. -/
theorem sourcePoissonPhysicalProbe_bigO_of_square_moments
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hMom : ∀ᶠ Z : ℝ in atTop, ∀ t : SNormOne F S, t ∈ D →
      ∃ M : Finset R,
        (∀ m ∉ M, sourcePoissonPhysicalAdditiveFactor F S₀ hζ
          (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) t m = 0) ∧
        (∑ m ∈ M, ‖sourcePoissonPhysicalAdditiveFactor F S₀ hζ
          (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) t m‖ ^ 2 ≤ A * Z ^ (-(133 / 1000) : ℝ)) ∧
        (∑ m ∈ M, ‖reflectionCoefficientRow F hζ S₀ hBad η m Z‖ ^ 2 ≤
          B * Z ^ (533 / 500 + 1 / 50000 : ℝ))) :
    (fun Z : ℝ => sourcePoissonOriginalIntegral F S₀ hζ η v hBad
      (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z) =O[atTop]
      (fun Z : ℝ => Z ^ (933 / 2000 + 1 / 100000 : ℝ)) := by
  refine IsBigO.of_bound ((Real.sqrt A * Real.sqrt B) * (ν).real D) ?_
  filter_upwards [hMom, eventually_gt_atTop (0 : ℝ)] with Z hM hZ
  have hX : 0 < Z ^ (9 / 10 : ℝ) := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Z ^ (133 / 1000 : ℝ) := Real.rpow_pos_of_pos hZ _
  have h := sourcePoissonOriginalIntegral_norm_le_square_moments F S₀ hζ η v hBad hX hY hZ
    (A * Z ^ (-(133 / 1000) : ℝ)) (B * Z ^ (533 / 500 + 1 / 50000 : ℝ)) hM
  rw [sourcePoissonPhysicalMoment_exponent hZ hA hB] at h
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hZ.le _)]
  exact h.trans_eq (by ac_rfl)

end
end ArtinMatthews.SourceEulerAssembly
