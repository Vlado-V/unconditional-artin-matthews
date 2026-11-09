module

public import ArtinMatthews.SourceKPCoupledTameRest
public import ArtinMatthews.SourceKPCoupledUniformizerPhase
public import ArtinMatthews.SourceKPCoupledUniformizerPowers


set_option backward.privateInPublic true
@[expose] public section

/-! Literal tame shell values for the coupled global section. The
unit phase and the three-periodic global action are retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField AdeleRing
noncomputable section

theorem sourceKPCoupledBruhatDiagonal_zpow {L : Type*} [Field L] (u : Lˣ) :
    sourceBruhatDiagonal u = sourceMinusOneUnit L * u^(-2 : ℤ) := by
  apply Units.ext
  change -((u : L)⁻¹)^2 = (sourceMinusOneUnit L * u^(-2 : ℤ) : Lˣ).val
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_neg, inv_pow]
  change -(((u : L)^2)⁻¹) = -1 * (((u : L)^2)⁻¹)
  rw [neg_one_mul, zpow_ofNat]

theorem sourceKPCoupledBruhatDiagonal_scaled {L : Type*} [Field L] (π u : Lˣ) (l : ℕ) :
    sourceBruhatDiagonal (π^(-(l : ℤ))*u) = π^(2*(l : ℤ)) * (sourceMinusOneUnit L * u^(-2 : ℤ)) := by
  rw [sourceKPCoupledBruhatDiagonal_zpow, mul_zpow, ← zpow_mul,
    show -(l : ℤ)*(-2) = 2*(l : ℤ) by ring]
  ac_rfl

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ)

local notation "L" => P.adicCompletion K
local notation "π₀" => sourceLocalPrimeUnit K P
local notation "ν₀" => sourceKPFiniteVal K P
local notation "F₀" => sourceKPAdelicCompactSection K hζ s
local notation "χ₀" => sourceKPTameUniformizerCharacter K hζ P π₀
local notation "A₀" => sourceKPLocalUniformizerCycle K hζ P π₀ s

theorem sourceKPCoupledTameShell_value (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1)
    (l : ℕ) (u : Lˣ) (hu : ν₀ (u : L) = 1) :
    sourceKPCoupledTameRestValue K hζ P s r ((π₀^(-(l : ℤ))*u : Lˣ) : L) =
      (((χ₀ u)^(4*(l : ℤ)) : ℂˣ).val *
        Complex.exp (-(s+1/2)*((2*(l : ℤ) : ℤ) : ℂ)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ))) •
          (A₀^(2*(l : ℤ))).val ((F₀).val r) := by
  let x : Lˣ := π₀^(-(l : ℤ))*u
  let u₀ : Lˣ := sourceMinusOneUnit L * u^(-2 : ℤ)
  have hπ := sourceKPCoupledUniformizer_valuation K P
  have hπo := (sourceKPValuationOrder_eq ν₀ π₀ 1).mpr hπ
  have hxo : sourceKPValuationOrder ν₀ x = -(l : ℤ) := by
    dsimp only [x]
    rw [sourceKPValuationOrder_mul, sourceKPValuationOrder_zpow, hπo,
      sourceKPValuationOrder_of_unit ν₀ u hu, mul_one, add_zero]
  have hxinv : ν₀ ((x : L)⁻¹) ≤ 1 := by
    rw [← Units.val_inv_eq_inv_val, ← zpow_neg_one, sourceKPValuationOrder_spec,
      sourceKPValuationOrder_zpow, hxo, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hm : ν₀ (sourceMinusOneUnit L : L) = 1 := by
    change ν₀ (-1 : L) = 1
    rw [Valuation.map_neg, map_one]
  have hu₀ : ν₀ (u₀ : L) = 1 := by
    change ν₀ ((sourceMinusOneUnit L * u^(-2 : ℤ) : Lˣ) : L) = 1
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hm, hu, one_zpow, one_mul]
  have hχ : χ₀ (sourceMinusOneUnit L) = 1 := by
    rw [sourceKPTameUniformizerCharacter_apply, sourceFiniteKPHilbert_minus_right, one_pow, map_one]
  have hp : (χ₀ u₀)^(-(2*(l : ℤ))) = (χ₀ u)^(4*(l : ℤ)) := by
    dsimp only [u₀]
    rw [map_mul, hχ, one_mul, map_zpow, ← zpow_mul]
    congr 1
    ring
  have hd : sourceBruhatDiagonal x = π₀^(2*(l : ℤ))*u₀ := sourceKPCoupledBruhatDiagonal_scaled π₀ u l
  change sourceKPCoupledTameRestValue K hζ P s r (x : L) = _
  rw [sourceKPCoupledTameRest_value_open K hζ P s h6 r hr x hxinv, hd,
    sourceKPCoupledUniformizer_diagonal_unit K hζ P π₀ s (2*(l : ℤ)) u₀ hu₀ _
      (sourceKPCoupledTameRest_unit_fixed K hζ P s h6 r hr), hp,
    sourceKPCoupledUniformizer_action_zpow K hζ P π₀ s, LinearMap.smul_apply, smul_smul]

end
end ArtinMatthews
