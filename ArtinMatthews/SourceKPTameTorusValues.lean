module

public import ArtinMatthews.SourceKPTameTorusRepresentation
public import ArtinMatthews.SourceKPTameOperatorBasis


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine central action, pure cube norm, and compact unit-fixed
vector of the actual tame torus model. These are the torus identities
used in the manuscript's Jacquet integral. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups ValuativeRel
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))

theorem sourceKPTameTorusRepresentation_center (z : rootsOfUnity 3 (P.adicCompletion K))
    (f : ZMod 3 → ℂ) :
    sourceKPTameTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPRankOneCenter K hζ P z) f =
      (sourceKPCentralComplex K hζ P z : ℂ) • f := by
  let ν := sourceKPFiniteVal K P
  let r := sourceKPTameUniformizerCharacter K hζ P π
  let b := sourceFiniteKPRankOneBase K hζ P (sourceFiniteKPRankOneCenter K hζ P z)
  change sourceKPTameOperator (Ideal.absNorm P.asIdeal : ℝ) (sourceKPCentralComplex K hζ P z)
    (r (sourceKPUnitPart ν π b)) (sourceKPValuationOrder ν b) f = _
  have hb : b = 1 := sourceFiniteKPRankOneCenter_base K hζ P z
  rw [hb, sourceKPValuationOrder_one, sourceKPUnitPart_of_unit ν π 1 (map_one ν), map_one r,
    sourceKPTameOperator_scalar _ _ _ (Int.cast_zero) f]
  simp [sourceJacquetScale]

theorem sourceKPTameTorusRepresentation_uniformizer_unit (j : ℤ)
    (u : (P.adicCompletion K)ˣ) (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    sourceKPTameTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPRankOneLift K hζ P (π ^ j * u))
        (sourceJacquetBasis 0) =
      (sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ) ((j : ℝ) / 6) *
        ((sourceKPTameUniformizerCharacter K hζ P π u ^ (-j) : ℂˣ) : ℂ)) •
        sourceJacquetBasis (j : ZMod 3) := by
  let ν := sourceKPFiniteVal K P
  let e := sourceKPCentralComplex K hζ P
  let r := sourceKPTameUniformizerCharacter K hζ P π
  let b := sourceFiniteKPRankOneBase K hζ P (sourceFiniteKPRankOneLift K hζ P (π ^ j * u))
  change sourceKPTameOperator (Ideal.absNorm P.asIdeal : ℝ) (e 1)
    (r (sourceKPUnitPart ν π b)) (sourceKPValuationOrder ν b) (sourceJacquetBasis 0) = _
  have hb : b = π ^ j * u := sourceFiniteKPRankOneLift_base K hζ P _
  have horder := (sourceKPValuationOrder_eq ν π 1).mpr hπ
  have hB : sourceKPValuationOrder ν (π ^ j * u) = j := by
    rw [sourceKPValuationOrder_mul, sourceKPValuationOrder_zpow, horder,
      sourceKPValuationOrder_of_unit ν u hu, mul_one, add_zero]
  have hU : sourceKPUnitPart ν π (π ^ j * u) = u := by
    rw [sourceKPUnitPart_mul, sourceKPUnitPart_of_uniformizer_zpow ν π hπ,
      sourceKPUnitPart_of_unit ν π u hu, one_mul]
  rw [hb, hB, hU, map_one e, sourceKPTameOperator_basis]
  simp only [Units.val_one, one_mul, mul_zero, zero_add]
  have hi : -(j : ZMod 3) - 0 = ((-j : ℤ) : ZMod 3) :=
    (sub_zero _).trans (Int.cast_neg (R := ZMod 3) j).symm
  rw [hi, sourceKPCubicPower_int (r u) (sourceKPTameUniformizerCharacter_cube K hζ P π u)]

theorem sourceKPTameTorusRepresentation_unit_fixed (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    sourceKPTameTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPRankOneLift K hζ P u)
      (sourceJacquetBasis 0) = sourceJacquetBasis 0 := by
  have h := sourceKPTameTorusRepresentation_uniformizer_unit K hζ P h6 π hπ 0 u hu
  simpa [sourceJacquetScale] using h

theorem sourceKPTameTorusRepresentation_cube (y : (P.adicCompletion K)ˣ) (f : ZMod 3 → ℂ) :
    sourceKPTameTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPRankOneLift K hζ P (y ^ 3)) f =
      sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ)
        ((sourceKPValuationOrder (sourceKPFiniteVal K P) y : ℝ) / 2) • f := by
  let ν := sourceKPFiniteVal K P
  let e := sourceKPCentralComplex K hζ P
  let r := sourceKPTameUniformizerCharacter K hζ P π
  let j := sourceKPValuationOrder ν y
  let b := sourceFiniteKPRankOneBase K hζ P (sourceFiniteKPRankOneLift K hζ P (y ^ 3))
  let part : (P.adicCompletion K)ˣ →* (P.adicCompletion K)ˣ :=
    { toFun := sourceKPUnitPart ν π
      map_one' := sourceKPUnitPart_of_unit ν π 1 (map_one ν)
      map_mul' := sourceKPUnitPart_mul ν π }
  change sourceKPTameOperator (Ideal.absNorm P.asIdeal : ℝ) (e 1)
    (r (part b)) (sourceKPValuationOrder ν b) f = _
  have hb : b = y ^ 3 := sourceFiniteKPRankOneLift_base K hζ P _
  have ho : sourceKPValuationOrder ν (y ^ (3 : ℕ)) = 3 * j := by
    have h := sourceKPValuationOrder_zpow ν y ((3 : ℕ) : ℤ)
    have h3 : ((3 : ℕ) : ℤ) = (3 : ℤ) := rfl
    rw [zpow_natCast, h3] at h
    exact h
  have hj : ((3 * j : ℤ) : ZMod 3) = 0 := by
    rw [Int.cast_mul, show ((3 : ℤ) : ZMod 3) = 0 by decide, zero_mul]
  have hr : r (part y) ^ 3 = 1 := sourceKPTameUniformizerCharacter_cube K hζ P π (part y)
  rw [hb, ho, map_pow part, map_pow r, hr, map_one e, sourceKPTameOperator_scalar _ _ _ hj f,
    Units.val_one, one_mul]
  have hs : (((3 * j : ℤ) : ℝ) / 6) = (j : ℝ) / 2 := by push_cast; ring
  rw [hs]

end
end ArtinMatthews
