module

public import ArtinMatthews.StandardLocalResidueVolume


set_option backward.privateInPublic true
@[expose] public section

/-! The literal compact-open unit annulus test and its exact scalar
Fourier transform, obtained as the difference of two actual balls. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

def sourceLocalUnitAnnulus : Set (P.adicCompletion K) :=
  {x | sourceLocalValuation K P x = 1}

def sourceLocalUnitTest : P.adicCompletion K → ℂ :=
  (sourceLocalUnitAnnulus K P).indicator (fun _ => 1)

theorem sourceLocalUnitAnnulus_eq_diff : sourceLocalUnitAnnulus K P =
    sourceLocalBall K P 0 \ sourceLocalBall K P (-1) := by
  ext x
  change sourceLocalValuation K P x = 1 ↔ x ∈ sourceLocalBall K P 0 ∧ x ∉ sourceLocalBall K P (-1)
  rw [sourceLocalPrimeBall_iff]
  change sourceLocalValuation K P x = 1 ↔
    sourceLocalValuation K P x ≤ WithZero.exp (0 : ℤ) ∧ ¬ sourceLocalValuation K P x < 1
  rw [WithZero.exp_zero, not_lt]
  exact le_antisymm_iff

theorem sourceLocalUnitAnnulus_isCompact : IsCompact (sourceLocalUnitAnnulus K P) := by
  rw [sourceLocalUnitAnnulus_eq_diff]
  exact (sourceLocalBall_isCompact K P 0).diff (sourceLocalBall_isOpen K P (-1))

theorem sourceLocalUnitAnnulus_ne_zero {x : P.adicCompletion K} (hx : x ∈ sourceLocalUnitAnnulus K P) : x ≠ 0 := by
  intro he
  change sourceLocalValuation K P x = 1 at hx
  rw [he, map_zero] at hx
  exact zero_ne_one hx

theorem sourceLocalUnitTest_eq_diff : sourceLocalUnitTest K P =
    sourceLocalBallIndicator K P 0 - sourceLocalBallIndicator K P (-1) := by
  funext x
  unfold sourceLocalUnitTest sourceLocalBallIndicator
  rw [sourceLocalUnitAnnulus_eq_diff]
  by_cases hx : x ∈ sourceLocalBall K P (-1)
  · have h₀ := sourceLocalPrimeBall_subset_integer K P hx
    simp [hx, h₀]
  · by_cases h₀ : x ∈ sourceLocalBall K P 0 <;> simp [hx, h₀]

theorem sourceLocalUnitTest_locallyConstant : IsLocallyConstant (sourceLocalUnitTest K P) := by
  rw [sourceLocalUnitTest_eq_diff]
  exact (sourceLocalBallIndicator_locallyConstant K P 0).sub (sourceLocalBallIndicator_locallyConstant K P (-1))

theorem sourceLocalUnitTest_compactSupport : HasCompactSupport (sourceLocalUnitTest K P) := by
  rw [sourceLocalUnitTest_eq_diff]
  exact (sourceLocalBallIndicator_compactSupport K P 0).sub (sourceLocalBallIndicator_compactSupport K P (-1))

theorem sourceLocalBallFourier_integrable_kernel (n : ℤ) (y : P.adicCompletion K) :
    Integrable (fun x => sourceLocalBallIndicator K P n x * localFiniteCharacter K P (-(y * x)))
      (sourceLocalSelfDual K P) := by
  let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  let g (x : P.adicCompletion K) := localFiniteCharacter K P (-(y * x))
  have hg : Continuous g := (localFiniteCharacter_continuous K P).comp (continuous_const.mul continuous_id).neg
  have h : Integrable ((sourceLocalBall K P n).indicator g) (sourceLocalSelfDual K P) :=
    (hg.continuousOn.integrableOn_compact (sourceLocalBall_isCompact K P n)).integrable_indicator
      (sourceLocalBall_isOpen K P n).measurableSet
  have he : (fun x => sourceLocalBallIndicator K P n x * localFiniteCharacter K P (-(y * x))) =
      (sourceLocalBall K P n).indicator g := by
    funext x
    by_cases hx : x ∈ sourceLocalBall K P n <;> simp [sourceLocalBallIndicator, hx, g]
  rwa [he]

theorem sourceLocalUnitTestFourier_raw (y : P.adicCompletion K) :
    sourceLocalFourier K P (sourceLocalUnitTest K P) y =
      ((sourceLocalSelfDual K P).real (sourceLocalBall K P 0) : ℂ) *
        sourceLocalBallIndicator K P (sourceDifferentExponent K P : ℤ) y -
      ((sourceLocalSelfDual K P).real (sourceLocalBall K P (-1)) : ℂ) *
        sourceLocalBallIndicator K P ((sourceDifferentExponent K P : ℤ) + 1) y := by
  rw [sourceLocalUnitTest_eq_diff]
  have h : sourceLocalFourier K P (sourceLocalBallIndicator K P 0 - sourceLocalBallIndicator K P (-1)) y =
      sourceLocalFourier K P (sourceLocalBallIndicator K P 0) y -
        sourceLocalFourier K P (sourceLocalBallIndicator K P (-1)) y := by
    unfold sourceLocalFourier
    simp only [Pi.sub_apply, sub_mul]
    exact integral_sub (sourceLocalBallFourier_integrable_kernel K P 0 y)
      (sourceLocalBallFourier_integrable_kernel K P (-1) y)
  rw [h, sourceLocalBallFourier, sourceLocalBallFourier]
  simp only [sub_zero, sub_neg_eq_add]

end
end ArtinMatthews.SourcePhysical
