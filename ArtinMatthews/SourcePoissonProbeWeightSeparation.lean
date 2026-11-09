module

public import ArtinMatthews.SourceProbeLogFourier
public import ArtinMatthews.SourcePoissonPhysicalPairing


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "A" => SLocalAdditiveCompletionSpace F S

/-- The actual exterior ideals retained by the fixed `W₁`. -/
def sourcePoissonLogSupportedExponents {Y : ℝ} (hY : 0 < Y) : Finset E :=
  (sourcePoissonOriginalCompactWeight_finite F S₀ hY).toFinset

theorem sourcePoissonLogSupportedExponents_mem_iff {Y : ℝ} (hY : 0 < Y) (s : E) :
    s ∈ sourcePoissonLogSupportedExponents F S₀ hY ↔
      sourceProbeW1Complex ((q s : ℝ) / Y) ≠ 0 :=
  (sourcePoissonOriginalCompactWeight_finite F S₀ hY).mem_toFinset

theorem sourcePoissonLogSupportedExponents_ratio_mem {Y : ℝ} (hY : 0 < Y) (s : E)
    (hs : s ∈ sourcePoissonLogSupportedExponents F S₀ hY) :
    (q s : ℝ) / Y ∈ Set.Icc (3 / 2 : ℝ) (5 / 2) := by
  rw [← sourceProbeW1Complex_tsupport]
  exact subset_tsupport _ ((sourcePoissonLogSupportedExponents_mem_iff F S₀ hY s).mp hs)

/-- The actual common row coordinate `m/(t₀ ell_(XY))`. -/
def sourcePoissonOriginalLogPoint (X Y : ℝ) (t : SNormOne F S) (m : R) : A :=
  sLocalRingDiagonal F S (m : F) * sourceSLocalUnitAdditivePoint F S
    (((t : SWholeUnits F S) * sLocalPositiveScaling F hζ S (X * Y))⁻¹)

private theorem sourcePoissonProbe_normScale_eq {X Y : ℝ} (hY : 0 < Y) (s : E) :
    (q s : ℝ) * X = (X * Y) * ((q s : ℝ) / Y) := by
  field_simp [hY.ne']

theorem sourcePoissonOriginalTest_eq_logPoint {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (t : SNormOne F S) (s : E) (m : R) :
    sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m =
      sourceSLocalCompletionProbe F S (sourcePoissonOriginalLogPoint F S₀ hζ X Y t m *
        sourceSLocalUnitAdditivePoint F S (sLocalPositiveScaling F hζ S ((q s : ℝ) / Y))⁻¹) := by
  have hv : 0 < (q s : ℝ) / Y := div_pos (by exact_mod_cast sourcePrimeExponentNorm_pos F S₀ s) hY
  have hu : (((t : SWholeUnits F S) * sLocalPositiveScaling F hζ S ((q s : ℝ) * X))⁻¹) =
      (((t : SWholeUnits F S) * sLocalPositiveScaling F hζ S (X * Y))⁻¹) *
        (sLocalPositiveScaling F hζ S ((q s : ℝ) / Y))⁻¹ := by
    rw [sourcePoissonProbe_normScale_eq F S₀ hY s,
      sLocalPositiveScaling_mul F hζ S (mul_pos hX hY) hv, ← mul_assoc, mul_inv_rev]
    exact mul_comm _ _
  rw [sourcePoissonOriginalTest, hu, sourceSLocalUnitAdditivePoint_mul, ← mul_assoc]
  rfl

/-- Each separated additive mode retains the normalized signed Gauss sums and the literal `Y⁻¹`. -/
def sourcePoissonLogAdditiveMode {Y : ℝ} (hY : 0 < Y) (j : ℤ) (m : R) : ℂ :=
  (Y : ℂ)⁻¹ * ∑ s ∈ sourcePoissonLogSupportedExponents F S₀ hY,
    (sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)) *
      sourceProbeLogFourierPhase ((q s : ℝ) / Y) j

theorem sourcePoissonLogAdditiveMode_norm_le {Y : ℝ} (hY : 0 < Y) (j : ℤ) (m : R) :
    ‖sourcePoissonLogAdditiveMode F S₀ hζ hY j m‖ ≤
      ‖(Y : ℂ)⁻¹‖ * ∑ s ∈ sourcePoissonLogSupportedExponents F S₀ hY,
        ‖sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)‖ := by
  rw [sourcePoissonLogAdditiveMode, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans_eq ?_
  simp only [norm_mul, sourceProbeLogFourierPhase_norm, mul_one]

variable [IsTotallyComplex F]

theorem sourcePoissonPhysicalAdditiveTerm_log_hasSum {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (t : SNormOne F S) (s : E) (m : R) (hs : s ∈ sourcePoissonLogSupportedExponents F S₀ hY) :
    HasSum (fun j => (Real.sqrt (X * Y) : ℂ)⁻¹ *
      (sourceProbeLogFourierCoeff F hζ S (sourcePoissonOriginalLogPoint F S₀ hζ X Y t m) j *
        ((sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)) *
          sourceProbeLogFourierPhase ((q s : ℝ) / Y) j)))
      (sourcePoissonPhysicalAdditiveTerm F S₀ hζ X Y t s m) := by
  let a : ℂ := (Real.sqrt (X * Y) : ℂ)⁻¹
  let g : ℂ := sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)
  let y := sourcePoissonOriginalLogPoint F S₀ hζ X Y t m
  have h := (sourceProbeLogFourier_hasSum F hζ S y
    (sourcePoissonLogSupportedExponents_ratio_mem F S₀ hY s hs)).mul_left (a * g)
  have ht := sourcePoissonOriginalTest_eq_logPoint F S₀ hζ hX hY t s m
  change sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m =
    sourceSLocalCompletionProbe F S (y * _) at ht
  rw [← ht] at h
  have hscale : (Real.sqrt ((q s : ℝ) * X) : ℂ)⁻¹ = a * (Real.sqrt ((q s : ℝ) / Y) : ℂ)⁻¹ := by
    rw [sourcePoissonProbe_normScale_eq F S₀ hY s, Real.sqrt_mul (mul_nonneg hX.le hY.le),
      Complex.ofReal_mul, mul_inv]
  have hval : (a * g) * ((Real.sqrt ((q s : ℝ) / Y) : ℂ)⁻¹ *
      sourceProbeW1Complex ((q s : ℝ) / Y) * sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m) =
      sourcePoissonPhysicalAdditiveTerm F S₀ hζ X Y t s m := by
    rw [sourcePoissonPhysicalAdditiveTerm, hscale]
    change _ = sourceProbeW1Complex ((q s : ℝ) / Y) *
      (a * (Real.sqrt ((q s : ℝ) / Y) : ℂ)⁻¹) *
        (g * sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m)
    ac_rfl
  rw [hval] at h
  convert h using 1
  funext j
  change a * (_ * (g * _)) = (a * g) * (_ * _)
  ac_rfl

/-- Exact Fourier separation of the original physical additive factor. -/
theorem sourcePoissonPhysicalAdditiveFactor_eq_logModes {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (t : SNormOne F S) (m : R) :
    sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m =
      (Real.sqrt (X * Y) : ℂ)⁻¹ * ∑' j : ℤ,
        sourceProbeLogFourierCoeff F hζ S (sourcePoissonOriginalLogPoint F S₀ hζ X Y t m) j *
          sourcePoissonLogAdditiveMode F S₀ hζ hY j m := by
  let P := sourcePoissonLogSupportedExponents F S₀ hY
  let a : ℂ := (Real.sqrt (X * Y) : ℂ)⁻¹
  let c (j : ℤ) := sourceProbeLogFourierCoeff F hζ S (sourcePoissonOriginalLogPoint F S₀ hζ X Y t m) j
  let g (s : E) (j : ℤ) :=
    (sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)) *
      sourceProbeLogFourierPhase ((q s : ℝ) / Y) j
  let b (s : E) (j : ℤ) := a * (c j * g s j)
  have hb (s : E) (hs : s ∈ P) : HasSum (b s) (sourcePoissonPhysicalAdditiveTerm F S₀ hζ X Y t s m) :=
    sourcePoissonPhysicalAdditiveTerm_log_hasSum F S₀ hζ hX hY t s m hs
  have hz (s : E) (hs : s ∉ P) : sourcePoissonPhysicalAdditiveTerm F S₀ hζ X Y t s m = 0 := by
    have hw : sourceProbeW1Complex ((q s : ℝ) / Y) = 0 := by
      by_contra h
      exact hs ((sourcePoissonLogSupportedExponents_mem_iff F S₀ hY s).mpr h)
    rw [sourcePoissonPhysicalAdditiveTerm, hw, zero_mul, zero_mul]
  rw [sourcePoissonPhysicalAdditiveFactor, tsum_eq_sum (s := P) hz]
  calc
    _ = (Y : ℂ)⁻¹ * ∑ s ∈ P, ∑' j : ℤ, b s j := by
      congr 1
      exact Finset.sum_congr rfl fun s hs => (hb s hs).tsum_eq.symm
    _ = (Y : ℂ)⁻¹ * ∑' j : ℤ, ∑ s ∈ P, b s j := by
      rw [Summable.tsum_finsetSum (fun s hs => (hb s hs).summable)]
    _ = a * ∑' j : ℤ, c j * sourcePoissonLogAdditiveMode F S₀ hζ hY j m := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro j
      change (Y : ℂ)⁻¹ * (∑ s ∈ P, a * (c j * g s j)) =
        a * (c j * ((Y : ℂ)⁻¹ * ∑ s ∈ P, g s j))
      simp only [← Finset.mul_sum]
      ac_rfl

theorem sourcePoissonPhysicalAdditiveFactor_log_summable_norm {Y : ℝ} (hY : 0 < Y)
    (X : ℝ) (t : SNormOne F S) (m : R) :
    Summable (fun j : ℤ => ‖sourceProbeLogFourierCoeff F hζ S
      (sourcePoissonOriginalLogPoint F S₀ hζ X Y t m) j *
        sourcePoissonLogAdditiveMode F S₀ hζ hY j m‖) := by
  let C := ‖(Y : ℂ)⁻¹‖ * ∑ s ∈ sourcePoissonLogSupportedExponents F S₀ hY,
    ‖sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)‖
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    ((sourceProbeLogFourierCoeff_summable_norm F hζ S
      (sourcePoissonOriginalLogPoint F S₀ hζ X Y t m)).mul_right C)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (sourcePoissonLogAdditiveMode_norm_le F S₀ hζ hY j m) (norm_nonneg _)

theorem sourcePoissonPhysicalAdditiveFactor_zero_off_logAnnulus {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (t : SNormOne F S) (m : R)
    (hm : sourcePoissonOriginalLogPoint F S₀ hζ X Y t m ∉ sourceProbeEnlargedAnnulus F hζ S) :
    sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m = 0 := by
  rw [sourcePoissonPhysicalAdditiveFactor_eq_logModes F S₀ hζ hX hY t m]
  simp only [sourceProbeLogFourierCoeff_eq_zero_outside F hζ S hm, zero_mul, tsum_zero, mul_zero]

end
end ArtinMatthews.SourceEulerAssembly
