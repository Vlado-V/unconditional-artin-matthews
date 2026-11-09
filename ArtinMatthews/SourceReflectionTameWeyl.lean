module

public import ArtinMatthews.SourceReflectionTameSign


set_option backward.privateInPublic true
@[expose] public section

/-! Weyl rotation of the actual tame Whittaker value. The cocycle
factor is kept through the Bruhat decomposition and then evaluated
on the literal uniformizer and unit parts. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "D₀" => fun a : Lˣ => l₀ (sourceGL2Diagonal a)
local notation "N₀" => fun x : L => l₀ (sourceGL2Upper x)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "B₀" => sourceFiniteKPHilbert K hζ P.val
local notation "ι₀" => sourceKPCentralComplex K hζ P.val
local notation "r₀" => sourceKPTameUniformizerCharacter K hζ P.val π₀
local notation "R₀" => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
local notation "f₀" => sourceKPTameCyclicSphericalVector K hζ S₀ P

theorem sourceKPTameCyclicWhittakerValue_compact_right (g : G₀)
    (k : SourceFiniteKP2Integral K P.val) :
    W₀ (g * sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k) = W₀ g := by
  have hk : R₀ (sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k) f₀ = f₀ :=
    Subtype.ext (sourceKPTameSphericalSection_right K hζ P.val h₆ π₀ hπ₀ k)
  rw [sourceKPTameCyclicWhittakerValue, map_mul R₀, Module.End.mul_apply, hk]
  rfl

theorem sourceKPTameCyclicWhittakerValue_center (z : rootsOfUnity 3 L) (g : G₀) :
    W₀ (sourceFiniteKP2ProjectiveCenter K hζ P.val z * g) = (ι₀ z : ℂ) * W₀ g := by
  have hz : R₀ (sourceFiniteKP2ProjectiveCenter K hζ P.val z) (R₀ g f₀) =
      (ι₀ z : ℂ) • (R₀ g f₀) :=
    Subtype.ext (sourceKPTameInducedRepresentation_center K hζ P.val h₆ π₀ hπ₀ z (R₀ g f₀).val)
  rw [sourceKPTameCyclicWhittakerValue, map_mul R₀, Module.End.mul_apply, hz, map_smul]
  rfl

theorem sourceKPTameCyclicWhittakerValue_weyl_upper (t H : Lˣ)
    (hH : ν₀ ((H : L)⁻¹) ≤ 1) :
    W₀ (D₀ t * w₀ * N₀ (H : L)) =
      ψ₀ ((t : L) * (H : L)⁻¹) *
        ((ι₀ (B₀ t (sourceBruhatDiagonal H) ^ 2) : ℂ) * W₀ (D₀ (t * sourceBruhatDiagonal H))) := by
  let x := (H : L)⁻¹
  let k : SourceFiniteKP2Integral K P.val :=
    ⟨sourceGL2Lower x, sourceKPIntegralMatrix_lower ν₀ x hH⟩
  let κ := sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k
  have hk : κ = l₀ (sourceGL2Lower x) :=
    sourceFiniteKP2ProjectiveCompactSection_lower K hζ P.val h₆ x hH
  have hshift : D₀ t * N₀ x = N₀ ((t : L) * x) * D₀ t := by
    rw [sourceFiniteKP2ProjectiveLift_upper_diagonal, mul_div_cancel_left₀ x (Units.ne_zero t)]
  have hbruhat : D₀ t * w₀ * N₀ (H : L) =
      N₀ ((t : L) * x) * (D₀ t * D₀ (sourceBruhatDiagonal H)) * κ := by
    rw [mul_assoc, sourceFiniteKP2ProjectiveLift_weyl_upper, hk]
    change D₀ t * (N₀ x * D₀ (sourceBruhatDiagonal H) * l₀ (sourceGL2Lower x)) = _
    simp only [← mul_assoc]
    rw [hshift]
  rw [hbruhat, sourceKPTameCyclicWhittakerValue_compact_right,
    sourceKPTameCyclicWhittakerValue_upper, sourceFiniteKP2ProjectiveLift_diagonal_mul,
    sourceKPTameCyclicWhittakerValue_center]

private theorem whittaker_diagonal_unit_phase (e : ℤ) (v : Lˣ) (hv : ν₀ (v : L) = 1) :
    W₀ (D₀ (π₀ ^ e * v)) = (r₀ v : ℂ) ^ (-e) * W₀ (D₀ (π₀ ^ e)) := by
  rw [sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS e v hv,
    sourceKPTameExteriorCharacter_residue K hζ S₀ P v hv, ← zpow_mul]
  rw [show (-2 : ℤ) * (-e) = 2 * e by ring]

private theorem unit_part_uniformizer_mul (e : ℤ) (v : Lˣ) (hv : ν₀ (v : L) = 1) :
    sourceKPUnitPart ν₀ π₀ (π₀ ^ e * v) = v := by
  rw [sourceKPUnitPart_mul, sourceKPUnitPart_of_uniformizer_zpow ν₀ π₀ hπ₀,
    sourceKPUnitPart_of_unit ν₀ π₀ v hv, one_mul]

/-- The active shift keeps its exact cofactor phase and its full diagonal
Whittaker value. The residue character of the translating unit has
exponent minus two for every signed frequency order. -/
theorem sourceKPTameCyclicWhittakerValue_weyl_translate (e : ℤ) (u v : Lˣ)
    (hu : ν₀ (u : L) = 1) (hv : ν₀ (v : L) = 1) :
    W₀ (D₀ (π₀ ^ (e - 2) * v) * w₀ * N₀ ((π₀ ^ (-1 : ℤ) * u : Lˣ) : L)) =
      ψ₀ ((π₀ : L) ^ (e - 1) * (v : L) / (u : L)) *
        χ₀ (sourceKPLocalUnitResidue K P.val u hu) ^ (-2 : ℤ) *
        (χ₀ (sourceKPLocalUnitResidue K P.val v hv) ^ (4 : ℤ) * W₀ (D₀ (π₀ ^ e * v))) := by
  let H := π₀ ^ (-1 : ℤ) * u
  let t := π₀ ^ (e - 2) * v
  let a := sourceMinusOneUnit L * u ^ (-2 : ℤ)
  have hH : ν₀ ((H : L)⁻¹) ≤ 1 := by
    have hval : ν₀ (H : L) = WithZero.exp (1 : ℤ) := by
      rw [sourceKPValuationOrder_spec, sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ _ _ hu,
        neg_neg]
    rw [map_inv₀, hval]
    exact inv_le_one_of_one_le₀ (WithZero.one_le_exp_iff.mpr (by norm_num))
  have ha : ν₀ (a : L) = 1 := by
    have hminus : ν₀ (sourceMinusOneUnit L : L) = 1 := by
      change ν₀ (-1 : L) = 1
      rw [Valuation.map_neg, map_one]
    dsimp only [a]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hminus, hu, one_zpow, mul_one]
  have hva : ν₀ ((v * a : Lˣ) : L) = 1 := by
    rw [Units.val_mul, map_mul, hv, ha, mul_one]
  have hs : sourceBruhatDiagonal H = π₀ ^ (2 : ℤ) * a := by
    simpa only [mul_one] using sourceBruhatDiagonal_uniformizer π₀ u (1 : ℤ)
  have ht : t * (π₀ ^ (2 : ℤ) * a) = π₀ ^ e * (v * a) := by
    dsimp only [t]
    rw [mul_mul_mul_comm, ← zpow_add, sub_add_cancel]
  have hx : (t : L) * (H : L)⁻¹ = (π₀ : L) ^ (e - 1) * (v : L) / (u : L) := by
    have hp : (π₀ : L) ^ (e - 2) * (π₀ : L) = (π₀ : L) ^ (e - 1) := by
      calc
        _ = (π₀ : L) ^ (e - 2) * (π₀ : L) ^ (1 : ℤ) := by rw [zpow_one]
        _ = _ := by
          rw [← zpow_add₀ (Units.ne_zero π₀), show e - 2 + 1 = e - 1 by omega]
    simp only [t, H, Units.val_mul, Units.val_zpow_eq_zpow_val, mul_inv_rev, zpow_neg_one,
      Units.val_inv_eq_inv_val, inv_inv]
    rw [mul_comm (u : L)⁻¹ (π₀ : L), mul_mul_mul_comm, hp, div_eq_mul_inv, mul_assoc]
  have hphase : ι₀ (B₀ t (π₀ ^ (2 : ℤ) * a) ^ 2) = r₀ a ^ (e - 2) * r₀ v ^ (-2 : ℤ) := by
    rw [sourceKPTameHilbert_phase K hζ P.val h₆ π₀ hπ₀,
      unit_part_uniformizer_mul K hζ S₀ P _ _ hv, unit_part_uniformizer_mul K hζ S₀ P _ _ ha,
      sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ _ _ hv,
      sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ _ _ ha]
  have hminus : r₀ (sourceMinusOneUnit L) = 1 := by
    rw [sourceKPTameUniformizerCharacter_apply, sourceFiniteKPHilbert_minus_right, one_pow, map_one]
  have hared : r₀ a ^ (-2 : ℤ) = r₀ u := by
    dsimp only [a]
    rw [map_mul r₀, hminus, one_mul, map_zpow r₀, ← zpow_mul,
      show (-2 : ℤ) * (-2) = ((4 : ℕ) : ℤ) by decide, zpow_natCast,
      show (4 : ℕ) = 3 + 1 by decide, pow_succ, sourceKPTameUniformizerCharacter_cube, one_mul]
  have hcombine :
      (r₀ a ^ (e - 2) * r₀ v ^ (-2 : ℤ)) * r₀ (v * a) ^ (-e) =
        (r₀ u * r₀ v ^ (-2 : ℤ)) * r₀ v ^ (-e) := by
    rw [map_mul r₀ v a, mul_zpow (r₀ v) (r₀ a)]
    calc
      _ = r₀ a ^ (-e) * (r₀ a ^ (e - 2) * r₀ v ^ (-2 : ℤ) * r₀ v ^ (-e)) := by
        rw [← mul_assoc, mul_comm (_ * _ * _) (r₀ a ^ (-e))]
      _ = (r₀ a ^ (e - 2) * r₀ a ^ (-e)) * r₀ v ^ (-2 : ℤ) * r₀ v ^ (-e) := by
        simp only [← mul_assoc, mul_comm (r₀ a ^ (-e)) (r₀ a ^ (e - 2))]
      _ = _ := by rw [← zpow_add, show e - 2 + -e = -2 by ring, hared]
  have hc := congrArg (fun z : ℂˣ => (z : ℂ)) hcombine
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val] at hc
  change W₀ (D₀ t * w₀ * N₀ (H : L)) = _
  rw [sourceKPTameCyclicWhittakerValue_weyl_upper K hζ S₀ P hS t H hH, hs, ht, hx, hphase,
    whittaker_diagonal_unit_phase K hζ S₀ P hS e (v * a) hva,
    whittaker_diagonal_unit_phase K hζ S₀ P hS e v hv,
    Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
  calc
    _ = ψ₀ ((π₀ : L) ^ (e - 1) * (v : L) / (u : L)) *
        (((r₀ a : ℂ) ^ (e - 2) * (r₀ v : ℂ) ^ (-2 : ℤ)) * (r₀ (v * a) : ℂ) ^ (-e)) *
        W₀ (D₀ (π₀ ^ e)) := by ring
    _ = _ := by
      rw [hc, sourceKPTameExteriorCharacter_residue K hζ S₀ P u hu,
        sourceKPTameExteriorCharacter_residue K hζ S₀ P v hv, ← zpow_mul,
        show (-2 : ℤ) * (-2) = 4 by decide]
      ring

/-- The signed inversion uses the diagonal minus one in the actual cover. -/
theorem sourceKPTameCyclicWhittakerValue_signed_weyl_translate (e : ℤ) (u v : Lˣ)
    (hu : ν₀ (u : L) = 1) (hv : ν₀ (v : L) = 1) :
    W₀ (D₀ (π₀ ^ (e - 2) * v) * (D₀ (sourceMinusOneUnit L) * w₀) *
      N₀ ((π₀ ^ (-1 : ℤ) * u : Lˣ) : L)) =
      ψ₀ (-((π₀ : L) ^ (e - 1) * (v : L) / (u : L))) *
        χ₀ (sourceKPLocalUnitResidue K P.val u hu) ^ (-2 : ℤ) *
        (χ₀ (sourceKPLocalUnitResidue K P.val v hv) ^ (4 : ℤ) * W₀ (D₀ (π₀ ^ e * v))) := by
  have hvneg : ν₀ ((-v : Lˣ) : L) = 1 := by
    rw [Units.val_neg, Valuation.map_neg, hv]
  have hdiag : D₀ (π₀ ^ (e - 2) * v) * D₀ (sourceMinusOneUnit L) =
      D₀ (π₀ ^ (e - 2) * (-v)) := by
    rw [sourceFiniteKP2ProjectiveLift_diagonal_mul, sourceFiniteKPHilbert_minus_right, one_pow,
      map_one, one_mul, mul_assoc]
    congr 2
    apply Units.ext
    simp [sourceMinusOneUnit]
  have hres : sourceKPLocalUnitResidue K P.val (-v) hvneg =
      -sourceKPLocalUnitResidue K P.val v hv := by
    unfold sourceKPLocalUnitResidue
    rw [show sourceKPLocalUnitInteger K P.val (-v) hvneg =
      -sourceKPLocalUnitInteger K P.val v hv from Subtype.ext (Units.val_neg v), map_neg]
  rw [← mul_assoc (D₀ (π₀ ^ (e - 2) * v)), hdiag,
    sourceKPTameCyclicWhittakerValue_weyl_translate K hζ S₀ P hS e u (-v) hu hvneg,
    hres, ← neg_one_mul (sourceKPLocalUnitResidue K P.val v hv),
    map_mul, sourceJacquetActualCharacter_minus_one, one_mul, Units.val_neg, mul_neg, neg_div,
    mul_neg, sourceKPTameCyclicWhittakerValue_diagonal_neg]

/-- At the inactive shift the Weyl lift belongs to the actual tame compact section. -/
theorem sourceKPTameCyclicWhittakerValue_weyl_right (g : G₀) : W₀ (g * w₀) = W₀ g := by
  let k : SourceFiniteKP2Integral K P.val := ⟨sourceGL2Weyl, sourceKPIntegralMatrix_weyl ν₀⟩
  have hk : sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k = w₀ :=
    congrArg (sourceFiniteKP2ProjectiveMk K hζ P.val) (sourceFiniteKP2CompactSection_weyl K hζ P.val h₆)
  rw [← hk, sourceKPTameCyclicWhittakerValue_compact_right]

end
end ArtinMatthews
