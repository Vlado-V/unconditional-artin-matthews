module

public import ArtinMatthews.SourceReflectionTameRotation
public import ArtinMatthews.SourceReflectionRationalPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Rescale the actual rotated diagonal by the square of its active
denominator. The remaining frequency-dependent central phase is the
rational Hilbert factor, while the active cofactor is a unit residue. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "res₀" => sourceKPLocalUnitResidue K P.val
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "D₀" => fun a : Lˣ => l₀ (sourceGL2Diagonal a)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "N₀" => fun x : L => l₀ (sourceGL2Upper x)
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
local notation "κ₀" => sourceReflectionLocalTorusPhase K hζ P.val
local notation "r₀" => sourceKPTameUniformizerCharacter K hζ P.val π₀
local notation "C₀" => sourceReflectionTameFourierCoefficient K hζ S₀ P
local notation "A₀" => sourceReflectionTameActiveFourier K hζ S₀ P

local instance normalizedResidueField : Field R :=
  letI : P.val.asIdeal.IsMaximal := P.val.isMaximal
  Ideal.Quotient.field _
local instance normalizedResidueFinite : Finite R := Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
local instance normalizedResidueFintype : Fintype R := Fintype.ofFinite _

private theorem torus_phase_mul_left (x y z : Lˣ) :
    κ₀ (x * y) z = κ₀ x z * κ₀ y z := by
  simp only [sourceReflectionLocalTorusPhase, map_mul, MonoidHom.mul_apply, mul_pow]

private theorem torus_phase_mul_right (x y z : Lˣ) :
    κ₀ x (y * z) = κ₀ x y * κ₀ x z := by
  simp only [sourceReflectionLocalTorusPhase, map_mul, mul_pow]

private theorem torus_phase_scale (t b a : Lˣ) :
    κ₀ t (b * a) * (κ₀ (t * b) a)⁻¹ = κ₀ t b * (κ₀ b a)⁻¹ := by
  rw [torus_phase_mul_right K hζ S₀ P, torus_phase_mul_left K hζ S₀ P, mul_inv_rev,
    mul_comm (κ₀ b a)⁻¹ (κ₀ t a)⁻¹, ← mul_assoc, mul_inv_cancel_right]

theorem sourceKPTameCyclicWhittakerValue_diagonal_right_unit (t a : Lˣ)
    (ha : ν₀ (a : L) = 1) :
    W₀ (D₀ t) = (κ₀ t a : ℂ) * W₀ (D₀ (t * a)) := by
  let k : SourceFiniteKP2Integral K P.val :=
    ⟨sourceGL2Diagonal a, sourceKPIntegralMatrix_diagonal ν₀ a ha⟩
  have hk : sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k = D₀ a :=
    congrArg (sourceFiniteKP2ProjectiveMk K hζ P.val)
      (sourceFiniteKP2CompactSection_diagonal K hζ P.val h₆ a ha)
  rw [← sourceKPTameCyclicWhittakerValue_compact_right K hζ S₀ P hS (D₀ t) k, hk,
    sourceFiniteKP2ProjectiveLift_diagonal_mul, sourceKPTameCyclicWhittakerValue_center]
  rfl

private theorem diagonal_mul_unit (t a : Lˣ) (ha : ν₀ (a : L) = 1) :
    W₀ (D₀ (t * a)) = ((κ₀ t a)⁻¹ : ℂ) * W₀ (D₀ t) := by
  rw [sourceKPTameCyclicWhittakerValue_diagonal_right_unit K hζ S₀ P hS t a ha,
    ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero (κ₀ t a)), one_mul]

theorem sourceKPTameCyclicWhittakerValue_weyl_normalized (t d u : Lˣ)
    (hd : ν₀ (d : L) = 1) (hu : ν₀ (u : L) = 1) :
    let b := π₀ * d
    W₀ (D₀ t * w₀ * N₀ ((π₀ ^ (-1 : ℤ) * u : Lˣ) : L)) =
      ψ₀ ((t : L) * (π₀ : L) / (u : L)) *
        ((κ₀ t (b ^ (2 : ℤ)) : ℂ) * χ₀ (res₀ d hd) ^ (-2 : ℤ) * χ₀ (res₀ u hu) ^ (-2 : ℤ)) *
        W₀ (D₀ (t * b ^ (2 : ℤ))) := by
  let H := π₀ ^ (-1 : ℤ) * u
  let b := π₀ * d
  let a := sourceMinusOneUnit L * (d * u) ^ (-2 : ℤ)
  have hH : ν₀ ((H : L)⁻¹) ≤ 1 := by
    have hval : ν₀ (H : L) = WithZero.exp (1 : ℤ) := by
      rw [sourceKPValuationOrder_spec, sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ _ _ hu, neg_neg]
    rw [map_inv₀, hval]
    exact inv_le_one_of_one_le₀ (WithZero.one_le_exp_iff.mpr (by norm_num))
  have ha : ν₀ (a : L) = 1 := by
    have hminus : ν₀ (sourceMinusOneUnit L : L) = 1 := by
      change ν₀ (-1 : L) = 1
      rw [Valuation.map_neg, map_one]
    simp only [a, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀,
      hminus, hd, hu, mul_one, one_zpow]
  have hBru : sourceBruhatDiagonal H = b ^ (2 : ℤ) * a := by
    have h := sourceBruhatDiagonal_uniformizer π₀ u (1 : ℤ)
    rw [mul_one] at h
    rw [h]
    symm
    dsimp only [b, a]
    rw [mul_zpow π₀ d, mul_zpow d u]
    calc
      _ = π₀ ^ (2 : ℤ) * ((d ^ (2 : ℤ) * d ^ (-2 : ℤ)) *
          (sourceMinusOneUnit L * u ^ (-2 : ℤ))) := by
        simp only [mul_assoc, mul_left_comm, mul_comm]
      _ = _ := by rw [← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  have harg : (t : L) * (H : L)⁻¹ = (t : L) * (π₀ : L) / (u : L) := by
    simp only [H, Units.val_mul, mul_inv_rev, zpow_neg_one,
      Units.val_inv_eq_inv_val, inv_inv, div_eq_mul_inv]
    rw [mul_comm (u : L)⁻¹ (π₀ : L), mul_assoc]
  have hb : sourceKPValuationOrder ν₀ b = 1 := by
    dsimp only [b]
    rw [sourceKPValuationOrder_mul, (sourceKPValuationOrder_eq ν₀ π₀ 1).mpr hπ₀,
      sourceKPValuationOrder_of_unit ν₀ d hd, add_zero]
  have hb₂ : sourceKPValuationOrder ν₀ (b ^ (2 : ℤ)) = 2 := by
    rw [sourceKPValuationOrder_zpow, hb, mul_one]
  have hκ : κ₀ (b ^ (2 : ℤ)) a = r₀ a ^ (2 : ℤ) := by
    rw [sourceReflectionLocalTorusPhase, sourceKPTameHilbert_phase K hζ P.val h₆ π₀ hπ₀,
      sourceKPUnitPart_of_unit ν₀ π₀ a ha, hb₂, sourceKPValuationOrder_of_unit ν₀ a ha,
      neg_zero, zpow_zero, mul_one]
  have hminus : r₀ (sourceMinusOneUnit L) = 1 := by
    rw [sourceKPTameUniformizerCharacter_apply, sourceFiniteKPHilbert_minus_right, one_pow, map_one]
  have hred : (κ₀ (b ^ (2 : ℤ)) a)⁻¹ = r₀ d * r₀ u := by
    rw [hκ, ← zpow_neg]
    dsimp only [a]
    rw [map_mul r₀, hminus, one_mul, map_zpow r₀, ← zpow_mul,
      show (-2 : ℤ) * (-2) = ((4 : ℕ) : ℤ) by decide, zpow_natCast,
      show (4 : ℕ) = 3 + 1 by decide, pow_succ, sourceKPTameUniformizerCharacter_cube, one_mul, map_mul r₀]
  have hc : (κ₀ t (b ^ (2 : ℤ) * a) : ℂ) * ((κ₀ (t * b ^ (2 : ℤ)) a)⁻¹ : ℂ) =
      (κ₀ t (b ^ (2 : ℤ)) : ℂ) * χ₀ (res₀ d hd) ^ (-2 : ℤ) * χ₀ (res₀ u hu) ^ (-2 : ℤ) := by
    have h := torus_phase_scale K hζ S₀ P t (b ^ (2 : ℤ)) a
    rw [hred] at h
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val,
      sourceKPTameExteriorCharacter_residue K hζ S₀ P d hd,
      sourceKPTameExteriorCharacter_residue K hζ S₀ P u hu, mul_assoc]
      using congrArg (fun z : ℂˣ => (z : ℂ)) h
  change W₀ (D₀ t * w₀ * N₀ (H : L)) = _
  rw [sourceKPTameCyclicWhittakerValue_weyl_upper K hζ S₀ P hS t H hH, hBru, harg,
    ← mul_assoc t (b ^ (2 : ℤ)) a, diagonal_mul_unit K hζ S₀ P hS _ a ha, ← mul_assoc _ _ (W₀ _)]
  change ψ₀ ((t : L) * (π₀ : L) / (u : L)) *
    (((κ₀ t (b ^ (2 : ℤ) * a) : ℂ) * ((κ₀ (t * b ^ (2 : ℤ)) a)⁻¹ : ℂ)) *
      W₀ (D₀ (t * b ^ (2 : ℤ)))) = _
  rw [hc]
  ring

theorem sourceReflectionTameRotatedActive_normalized (j : Fin 6) (e : ℕ) (v d : Lˣ)
    (hv : ν₀ (v : L) = 1) (hd : ν₀ (d : L) = 1) :
    let t := π₀ ^ ((e : ℤ) - 2) * v
    let b := π₀ * d
    sourceReflectionTameRotatedActive K hζ S₀ P hS j e v =
      A₀ j (if e = 0 then res₀ v hv else 0) *
        ((κ₀ t (b ^ (2 : ℤ)) : ℂ) * χ₀ (res₀ d hd) ^ (-2 : ℤ) * W₀ (D₀ (t * b ^ (2 : ℤ)))) := by
  let t := π₀ ^ ((e : ℤ) - 2) * v
  let b := π₀ * d
  change sourceReflectionTameRotatedActive K hζ S₀ P hS j e v = _
  unfold sourceReflectionTameRotatedActive sourceReflectionTameActiveFourier
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  let u := sourceReflectionTameUnitLift K S₀ P h
  let hu := sourceReflectionTameUnitLift_valuation K S₀ P h
  have ht : (t : L) * (π₀ : L) = (π₀ : L) ^ ((e : ℤ) - 1) * (v : L) := by
    dsimp only [t]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, mul_right_comm]
    congr 1
    calc
      _ = (π₀ : L) ^ ((e : ℤ) - 2) * (π₀ : L) ^ (1 : ℤ) := by rw [zpow_one]
      _ = _ := by rw [← zpow_add₀ (Units.ne_zero π₀), show (e : ℤ) - 2 + 1 = (e : ℤ) - 1 by omega]
  have hχ : χ₀ (h : R) ^ (-2 : ℤ) = ((χ₀⁻¹) ^ (2 : ℕ)) h := by
    change χ₀ (h : R) ^ (-((2 : ℕ) : ℤ)) = _
    rw [zpow_neg, zpow_natCast, MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv', inv_pow]
  change C₀ j h * W₀ (D₀ t * w₀ * N₀ ((π₀ ^ (-1 : ℤ) * u : Lˣ) : L)) = _
  rw [sourceKPTameCyclicWhittakerValue_weyl_normalized K hζ S₀ P hS t d u hd hu, ht,
    sourceReflectionTameActivePhase K hζ S₀ P hS e u v hu hv,
    sourceReflectionTameUnitLift_residue K S₀ P h, hχ, div_eq_mul_inv, ← Units.val_inv_eq_inv_val]
  ring

theorem sourceReflectionTameRotatedInactive_normalized (j : Fin 6) (t b : Lˣ)
    (hb : ν₀ (b : L) = 1) :
    C₀ j 0 * W₀ (D₀ t * w₀ * N₀ 0) =
      (if j = 0 then 1 - (Ideal.absNorm P.val.asIdeal : ℂ)⁻¹ else 0) *
        ((κ₀ t (b ^ (2 : ℤ)) : ℂ) * W₀ (D₀ (t * b ^ (2 : ℤ)))) := by
  have hb₂ : ν₀ ((b ^ (2 : ℤ) : Lˣ) : L) = 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hb, one_zpow]
  rw [sourceReflectionTameRotatedInactive_eq K hζ S₀ P hS j t,
    sourceKPTameCyclicWhittakerValue_diagonal_right_unit K hζ S₀ P hS t _ hb₂]

end
end ArtinMatthews
