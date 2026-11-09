module

public import ArtinMatthews.SourceKPCoupledTameShellValue
public import ArtinMatthews.SourceKPCoupledTameShellMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! The actual nontrivial unit phase cancels every shell outside the
three-divisible radii, with the global remainder retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical
open scoped NumberField AdeleRing Classical
noncomputable section

theorem sourceKPCoupledCubicUnit_power_ne_one (z : ℂˣ) (hz : z^3 = 1) (hz₁ : z ≠ 1)
    (l : ℕ) (hl : ¬3 ∣ l) : ((z^(4*(l : ℤ)) : ℂˣ) : ℂ) ≠ 1 := by
  have ho : orderOf z = 3 := ((Nat.dvd_prime Nat.prime_three).mp
    (orderOf_dvd_iff_pow_eq_one.mpr hz)).resolve_left (fun h => hz₁ (orderOf_eq_one_iff.mp h))
  intro h
  have hp : z^(4*(l : ℤ)) = 1 := Units.ext h
  rw [show 4*(l : ℤ) = ((4*l : ℕ) : ℤ) by push_cast <;> rfl, zpow_natCast] at hp
  have hd := orderOf_dvd_iff_pow_eq_one.mpr hp
  rw [ho] at hd
  exact hl ((Nat.prime_three.dvd_mul.mp hd).resolve_left (by decide))

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ)

local notation "L" => P.adicCompletion K
local notation "π₀" => sourceLocalPrimeUnit K P
local notation "ν₀" => sourceKPFiniteVal K P
local notation "χ₀" => sourceKPTameUniformizerCharacter K hζ P π₀
local notation "A₀" => sourceKPLocalUniformizerCycle K hζ P π₀ s
local notation "F₀" => sourceKPAdelicCompactSection K hζ s
local notation "μ₀" => sourceJacquetHaar K P
local notation "shell₀" => sourceJacquetValuationShell K P
local notation "Q₀" => (Ideal.absNorm P.asIdeal : ℝ)

theorem sourceKPCoupledTameKernel_shell_unit_dilate (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1)
    (l : ℕ) (a : Lˣ) (ha : ν₀ (a : L) = 1) (x : L) (hx : x ∈ shell₀ (l : ℤ)) :
    sourceKPCoupledTameRestKernel K hζ P s r ((a : L)*x) =
      (((χ₀ a)^(4*(l : ℤ)) : ℂˣ) : ℂ) * sourceKPCoupledTameRestKernel K hζ P s r x := by
  obtain ⟨u, hu, rfl⟩ := sourceKPCoupledTameShell_unit_coordinates K P l x hx
  have hν : ν₀ ((a*u : Lˣ) : L) = 1 := by rw [Units.val_mul, map_mul, ha, hu, mul_one]
  have he : (a : L) * ((π₀^(-(l : ℤ))*u : Lˣ) : L) =
      ((π₀^(-(l : ℤ))*(a*u) : Lˣ) : L) := by simp only [Units.val_mul]; ring
  rw [he]
  unfold sourceKPCoupledTameRestKernel
  rw [sourceKPCoupledTameShell_value K hζ P s h6 r hr l (a*u) hν,
    sourceKPCoupledTameShell_value K hζ P s h6 r hr l u hu,
    map_mul χ₀, mul_zpow, Units.val_mul]
  let cₐ : ℂ := ((χ₀ a)^(4*(l : ℤ)) : ℂˣ)
  let cᵤ : ℂ := ((χ₀ u)^(4*(l : ℤ)) : ℂˣ)
  let z := Complex.exp (-(s+1/2)*((2*(l : ℤ) : ℤ) : ℂ)*(Real.log Q₀ : ℂ))
  let v := ((A₀^(2*(l : ℤ))).val ((F₀).val r)).val 1
  change (cₐ*cᵤ*z)*v = cₐ*((cᵤ*z)*v)
  ring

theorem sourceKPCoupledTameKernel_shell_divisible (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1)
    (l : ℕ) (hl : 3 ∣ l) (x : L) (hx : x ∈ shell₀ (l : ℤ)) :
    sourceKPCoupledTameRestKernel K hζ P s r x =
      Complex.exp (-(s+1/2)*((2*(l : ℤ) : ℤ) : ℂ)*(Real.log Q₀ : ℂ)) *
        sourceKPAdelicCompactScalar K hζ s r := by
  obtain ⟨u, hu, rfl⟩ := sourceKPCoupledTameShell_unit_coordinates K P l x hx
  obtain ⟨m, hm⟩ := hl
  have hA := sourceKPLocalUniformizerCycle_cube K hζ P π₀ (sourceKPCoupledUniformizer_valuation K P) s
  have ha : A₀^(2*(l : ℤ)) = 1 := by
    rw [show 2*(l : ℤ) = 3*(2*(m : ℤ)) by rw [hm]; push_cast; ring,
      zpow_mul, zpow_ofNat, hA, one_zpow]
  have hχ : (χ₀ u)^(4*(l : ℤ)) = 1 := by
    rw [show 4*(l : ℤ) = 3*(4*(m : ℤ)) by rw [hm]; push_cast; ring,
      zpow_mul, zpow_ofNat, sourceKPTameUniformizerCharacter_cube, one_zpow]
  unfold sourceKPCoupledTameRestKernel
  rw [sourceKPCoupledTameShell_value K hζ P s h6 r hr l u hu, ha, hχ, Units.val_one, one_mul] <;> rfl

theorem sourceKPCoupledTameKernel_shell_integral (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) (l : ℕ) :
    (∫ x in shell₀ (l : ℤ), sourceKPCoupledTameRestKernel K hζ P s r x ∂μ₀) =
      if 3 ∣ l then
        ((μ₀).real (shell₀ (l : ℤ)) : ℂ) *
          (Complex.exp (-(s+1/2)*((2*(l : ℤ) : ℤ) : ℂ)*(Real.log Q₀ : ℂ)) *
            sourceKPAdelicCompactScalar K hζ s r)
      else 0 := by
  let f := sourceKPCoupledTameRestKernel K hζ P s r
  have hmeas := (sourceJacquetValuationShell_isCompact K P (l : ℤ)).measurableSet
  by_cases hl : 3 ∣ l
  · rw [ite_eq_left hl,
      setIntegral_congr_fun hmeas (sourceKPCoupledTameKernel_shell_divisible K hζ P s h6 r hr l hl),
      integral_const, Measure.real, Measure.restrict_apply_univ]
    rfl
  · rw [ite_eq_right hl]
    obtain ⟨a, ha, hχ⟩ := sourceKPCoupledUniformizer_exists_nontrivial_unit K hζ P π₀
      (sourceKPCoupledUniformizer_valuation K P)
    let c : ℂ := ((χ₀ a)^(4*(l : ℤ)) : ℂˣ)
    have hc : c ≠ 1 := sourceKPCoupledCubicUnit_power_ne_one (χ₀ a)
      (sourceKPTameUniformizerCharacter_cube K hζ P π₀ a) hχ l hl
    let : (μ₀).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
    have ha₁ : ‖(a : L)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr ha
    have hImage := sourceJacquetValuationShell_mul_image K P (l : ℤ) 0 a
      (by rw [WithZero.exp_zero]; exact ha)
    rw [add_zero] at hImage
    have h := sourceLocalAddHaar_setIntegral_dilation K P μ₀ a (shell₀ (l : ℤ)) f
    rw [hImage, ha₁, one_smul] at h
    have he := setIntegral_congr_fun (μ := μ₀) hmeas
      (sourceKPCoupledTameKernel_shell_unit_dilate K hζ P s h6 r hr l a ha)
    change (∫ x in shell₀ (l : ℤ), f ((a : L)*x) ∂μ₀) = ∫ x in shell₀ (l : ℤ), c*f x ∂μ₀ at he
    rw [integral_const_mul] at he
    have hz := h.trans he
    have hzero : (c-1)*(∫ x in shell₀ (l : ℤ), f x ∂μ₀) = 0 := by
      rw [sub_mul, one_mul, ← hz, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)

end
end ArtinMatthews
