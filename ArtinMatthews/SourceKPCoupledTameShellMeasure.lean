module

public import ArtinMatthews.SourceKPCoupledTameRest
public import ArtinMatthews.SourceKPCoupledUniformizerPhase
public import ArtinMatthews.SourceLocalHaarGeneralDilation
public import ArtinMatthews.SourceKPFiniteUnipotentConstancy
public import ArtinMatthews.SourceFinitePlaceSplit


set_option backward.privateInPublic true
@[expose] public section

/-! Continuity and actual normalized additive masses of the tame
valuation shells at every finite place. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical Set
open scoped NumberField AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "π₀" => sourceLocalPrimeUnit K P
local notation "ν₀" => sourceKPFiniteVal K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "μ₀" => sourceJacquetHaar K P
local notation "B₀" => sourceLocalBall K P
local notation "shell₀" => sourceJacquetValuationShell K P
local notation "Q₀" => (Ideal.absNorm P.asIdeal : ℝ)

theorem sourceKPCoupledTameRestKernel_eq_upper (s : ℂ) (r : SourceKPAdelicProjective K hζ) (x : L) :
    sourceKPCoupledTameRestKernel K hζ P s r x =
      sourceKPAdelicCompactScalar K hζ s
        (ι₀ (l₀ sourceGL2Weyl) * sourceKPAdelicUpperLift K hζ (0, sourceKPFiniteAdditiveSingle K P x) * r) := by
  change sourceKPAdelicCompactScalar K hζ s (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * r) = _
  rw [map_mul, sourceKPAdelicLocalProjective_upper]

theorem sourceKPCoupledTameRestKernel_continuous (s : ℂ) (r : SourceKPAdelicProjective K hζ) :
    Continuous (sourceKPCoupledTameRestKernel K hζ P s r) := by
  rw [show sourceKPCoupledTameRestKernel K hζ P s r = _ from
    funext (sourceKPCoupledTameRestKernel_eq_upper K hζ P s r)]
  exact (sourceKPAdelicCompactScalar_finite_continuous K hζ s (ι₀ (l₀ sourceGL2Weyl)) r).comp
    (sourceKPFiniteAdditiveSingle_continuous K P)

theorem sourceKPCoupledTameShell_scaled_unit_image (l : ℕ) :
    (fun x : L => ((π₀^(-(l : ℤ)) : Lˣ) : L)*x) '' shell₀ 0 = shell₀ (l : ℤ) := by
  have ht : ν₀ ((π₀^(-(l : ℤ)) : Lˣ) : L) = WithZero.exp (l : ℤ) := by
    rw [Units.val_zpow_eq_zpow_val,
      sourceJacquetFrequency_valuation K P _ (sourceKPCoupledUniformizer_valuation K P), neg_neg]
  have h := sourceJacquetValuationShell_mul_image K P 0 (l : ℤ) (π₀^(-(l : ℤ))) ht
  rwa [zero_add] at h

theorem sourceKPCoupledTameShell_unit_coordinates (l : ℕ) (x : L) (hx : x ∈ shell₀ (l : ℤ)) :
    ∃ u : Lˣ, ν₀ (u : L) = 1 ∧ x = ((π₀^(-(l : ℤ))*u : Lˣ) : L) := by
  rw [← sourceKPCoupledTameShell_scaled_unit_image K P l] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hv : ν₀ u = 1 := by
    simpa only [WithZero.exp_zero] using (sourceJacquetValuationShell_mem K P 0 u).mp hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  exact ⟨Units.mk0 u hu0, hv, rfl⟩

theorem sourceKPCoupledJacquetBall_mass : (μ₀).real (B₀ 0) = 1 := by
  rw [sourceLocalBall_zero_eq_integerOpen, Measure.real, sourceJacquetHaar_integers, ENNReal.toReal_one]

theorem sourceKPCoupledJacquetShell_mass (l : ℕ) :
    (μ₀).real (shell₀ (l : ℤ)) = Q₀ ^ l * (1-Q₀⁻¹) := by
  let : (μ₀).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  have hsub : B₀ ((l : ℤ)-1) ⊆ B₀ (l : ℤ) := by
    intro x hx
    exact le_trans hx (WithZero.exp_le_exp.mpr (by omega))
  change (μ₀).real (B₀ (l : ℤ) \ B₀ ((l : ℤ)-1)) = _
  rw [measureReal_sdiff hsub (sourceLocalBall_isOpen K P _).measurableSet
      (sourceLocalBall_isCompact K P _).measure_ne_top,
    sourceLocalBall_volume_scaling K P μ₀ (l : ℤ), sourceLocalBall_volume_scaling K P μ₀ ((l : ℤ)-1)]
  simp only [sourceKPCoupledJacquetBall_mass K P, mul_one]
  rw [zpow_sub₀ (sourceLocalNorm_pos K P).ne', zpow_one, zpow_natCast, div_eq_mul_inv]
  ring

end
end ArtinMatthews
