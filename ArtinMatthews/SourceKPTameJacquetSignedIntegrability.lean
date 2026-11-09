module

public import ArtinMatthews.SourceKPTameJacquetShellIntegral
public import ArtinMatthews.SourceJacquetIntegrabilityDilation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual translated spherical integrand is locally integrable
also for negative torus valuations. On each compact shell it has a
continuous representative after an invertible finite-place dilation. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical VaryingKummerAnalytic Filter
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceLocalValuation K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "B" => sourceLocalBall K P.val
local notation "S₁" => sourceJacquetValuationShell K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

theorem sourceKPTameJacquetScaledIntegrableOn_ball_signed (hP : P.val ∉ traceBadPlaces K) (e : ℤ) (N : ℕ) :
    IntegrableOn (sourceKPTameJacquetScaledIntegrand K hζ S₀ P e) (B (N : ℤ)) μ₀ := by
  let f := sourceKPTameJacquetScaledIntegrand K hζ S₀ P e
  let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
  have hzero : IntegrableOn f (B 0) μ₀ := by
    let g : L → ZMod 3 → ℂ := fun H => ψ₀ (-((π₀ : L) ^ e * H)) •
      (sourceJacquetScale Q₀ ((e : ℝ) / 3) • sourceJacquetBasis ((-e : ℤ) : ZMod 3))
    have hg : Continuous g := ((localFiniteCharacter_continuous K P.val).comp
      (continuous_const.mul continuous_id).neg).smul continuous_const
    have hB := sourceLocalBall_isCompact K P.val 0
    apply (hg.continuousOn.integrableOn_compact (μ := μ₀) hB).congr_fun _ hB.measurableSet
    intro H hH
    have hH' : ν₀ H ≤ 1 := by
      change ν₀ H ≤ WithZero.exp (0 : ℤ) at hH
      rwa [WithZero.exp_zero] at hH
    change g H = ψ₀ (-((π₀ : L) ^ e * H)) •
      sourceKPTameJacquetPoint K hζ S₀ P e ((π₀ : L) ^ e * H)
    rw [sourceKPTameJacquetPoint_scaled_integral K hζ S₀ P e H hH']
  have hshell (l : ℕ) : IntegrableOn f (S₁ (l : ℤ)) μ₀ := by
    let t := π₀ ^ (-(l : ℤ))
    let χ := sourceJacquetShellCharacter K P.val (reflectionPrimeCharacters K hζ S₀ P) l
    let g : L → ZMod 3 → ℂ := fun u => ψ₀ (-((π₀ : L) ^ e * ((t : L) * u))) •
      ((sourceJacquetScale Q₀ (((e : ℝ) - 2 * (l : ℝ)) / 3) * sourceJacquetWeight K P.val χ u) •
        sourceJacquetBasis ((2 * (l : ℤ) - e : ℤ) : ZMod 3))
    have hg : Continuous g :=
      ((localFiniteCharacter_continuous K P.val).comp
        (continuous_const.mul (continuous_const.mul continuous_id)).neg).smul
          ((continuous_const.mul (sourceJacquetWeight_locallyConstant K P.val χ).continuous).smul continuous_const)
    have hs := sourceJacquetValuationShell_isCompact K P.val 0
    have hI : IntegrableOn (fun u : L => f ((t : L) * u)) (S₁ 0) μ₀ := by
      apply (hg.continuousOn.integrableOn_compact (μ := μ₀) hs).congr_fun _ hs.measurableSet
      intro u hu
      have hν : ν₀ u = 1 := by
        have h := (sourceJacquetValuationShell_mem K P.val 0 u).mp hu
        rwa [WithZero.exp_zero] at h
      have hu₀ : u ≠ 0 := by
        intro h
        rw [h, map_zero] at hν
        exact zero_ne_one hν
      let v := Units.mk0 u hu₀
      have hp := sourceKPTameJacquetPoint_scaled_shell K hζ S₀ P e l v hν
      change sourceKPTameJacquetPoint K hζ S₀ P e ((π₀ : L) ^ e * ((π₀ : L) ^ (-(l : ℤ)) * u)) = _ at hp
      have hv : (v : L) = u := rfl
      rw [hv] at hp
      change g u = ψ₀ (-((π₀ : L) ^ e * ((t : L) * u))) •
        sourceKPTameJacquetPoint K hζ S₀ P e ((π₀ : L) ^ e * ((t : L) * u))
      have htval : (t : L) = (π₀ : L) ^ (-(l : ℤ)) := Units.val_zpow_eq_zpow_val _ _
      dsimp only [g, χ]
      rw [htval, hp]
    have ht : ν₀ (t : L) = WithZero.exp (l : ℤ) := by
      dsimp only [t]
      rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀, neg_neg]
    have h := (sourceJacquetIntegrableOn_dilation_iff K P.val hP t (S₁ 0) f).mpr hI
    rw [sourceJacquetValuationShell_mul_image K P.val 0 (l : ℤ) t ht, zero_add] at h
    exact h
  exact (sourceJacquetBall_integral_shells K P.val f hzero (fun l _ => hshell l) N).1

theorem sourceKPTameJacquetIntegrableOn_eventually_signed (hP : P.val ∉ traceBadPlaces K) (e : ℤ) :
    ∀ᶠ N : ℕ in atTop, IntegrableOn (sourceKPTameJacquetIntegrand K hζ S₀ P e) (B (N : ℤ)) μ₀ := by
  let t := π₀ ^ e
  let f := sourceKPTameJacquetIntegrand K hζ S₀ P e
  have ht : ν₀ (t : L) = WithZero.exp (-e) := by
    dsimp only [t]
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀]
  filter_upwards [eventually_ge_atTop (-e).toNat] with N hN
  let M := ((N : ℤ) + e).toNat
  have hM : (M : ℤ) + -e = (N : ℤ) := by dsimp only [M]; omega
  have hf : (fun H : L => f ((t : L) * H)) = sourceKPTameJacquetScaledIntegrand K hζ S₀ P e := by
    funext H
    change f (((π₀ ^ e : Lˣ) : L) * H) = f ((π₀ : L) ^ e * H)
    rw [Units.val_zpow_eq_zpow_val]
  have h := (sourceJacquetIntegrableOn_dilation_iff K P.val hP t (B (M : ℤ)) f).mpr
    (hf.symm ▸ sourceKPTameJacquetScaledIntegrableOn_ball_signed K hζ S₀ P hP e M)
  rwa [sourceJacquetBall_mul_image K P.val (M : ℤ) (-e) t ht, hM] at h

end
end ArtinMatthews
