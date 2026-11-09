module

public import ArtinMatthews.SourceKPCompactCoChain
public import ArtinMatthews.SourceKPIntegralGeneration


set_option backward.privateInPublic true
@[expose] public section

/-! Exact compact cochain law on unit diagonals and ordinary scalars.
The determinant in the cochain contributes the required inverse
unit factor. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups Classical
noncomputable section
variable {F Γ A : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ] [CommGroup A]
    (ν : Valuation F Γ) (B : Fˣ →* (Fˣ →* A))

theorem sourceGL2_right_scalar_apply (g : GL (Fin 2) F) (u : Fˣ) (i j : Fin 2) :
    (g * GeneralLinearGroup.scalar (Fin 2) u) i j = g i j * (u : F) := by
  exact Matrix.mul_diagonal (fun _ : Fin 2 => (u : F)) (g : Matrix (Fin 2) (Fin 2) F) i j

theorem sourceKPCompactPhase_rescale_right
    (hdiag : ∀ x, B x x = 1)
    (hunit : ∀ a b : Fˣ, ν (a : F) = 1 → ν (b : F) = 1 → B a b = 1)
    (g g' : GL (Fin 2) F) (hg : SourceKPIntegralMatrix ν g) (hg' : SourceKPIntegralMatrix ν g')
    (u : Fˣ) (hu : ν (u : F) = 1)
    (hC : g' 1 0 = g 1 0 * (u : F))
    (hD : ∀ (hd : g 1 1 ≠ 0) (hd' : g' 1 1 ≠ 0),
      Units.mk0 (g' 1 1) hd' / GeneralLinearGroup.det g' =
        (Units.mk0 (g 1 1) hd / GeneralLinearGroup.det g) / u) :
    sourceKPCompactPhase ν B g' = if g 1 0 = 0 then 1
      else sourceKPCompactPhase ν B g * B u (sourceKubotaX g) := by
  have hV : ν (g' 1 0) = ν (g 1 0) := by rw [hC, map_mul, hu, mul_one]
  by_cases hc : g 1 0 = 0
  · have hc' : g' 1 0 = 0 := by rw [hC, hc, zero_mul]
    rw [ite_eq_left hc, sourceKPCompactPhase_zero_left ν B g' hc']
  rw [ite_eq_right hc]
  have hc' : g' 1 0 ≠ 0 := by rw [hC]; exact mul_ne_zero hc (Units.ne_zero u)
  by_cases hcu : ν (g 1 0) = 1
  · have hxu : ν ((sourceKubotaX g : Fˣ) : F) = 1 := by rw [sourceKubotaX_val_left g hc, hcu]
    rw [sourceKPCompactPhase_unit_left ν B g hcu, sourceKPCompactPhase_unit_left ν B g' (hV.trans hcu),
      hunit u _ hu hxu, mul_one]
  have hcv : ν (g 1 0) < 1 := lt_of_le_of_ne (hg.entries 1 0) hcu
  have hcv' : ν (g' 1 0) < 1 := hV.symm ▸ hcv
  have hd := (sourceKPIntegralMatrix_bottom_unit ν hg).resolve_left hcu
  have hd' := (sourceKPIntegralMatrix_bottom_unit ν hg').resolve_left (by rwa [hV])
  have hd0 := sourceKPVal_eq_one_ne_zero ν hd
  have hd0' := sourceKPVal_eq_one_ne_zero ν hd'
  have hx : sourceKubotaX g' = sourceKubotaX g * u := by
    apply Units.ext
    rw [Units.val_mul, sourceKubotaX_val_left g hc, sourceKubotaX_val_left g' hc', hC]
  rw [sourceKPCompactPhase_nonunit_left ν B g' hc' hcv' hd0',
    sourceKPCompactPhase_nonunit_left ν B g hc hcv hd0, hD hd0 hd0', hx]
  exact sourceKPCompactSymbol_scale ν B hdiag hunit (sourceKubotaX g) u _ hu
    (sourceKPVal_unit_div ν (Units.mk0 (g 1 1) hd0) (GeneralLinearGroup.det g) hd hg.det_unit)

theorem sourceKPCompactPhase_right_diagonal
    (hdiag : ∀ x, B x x = 1)
    (hunit : ∀ a b : Fˣ, ν (a : F) = 1 → ν (b : F) = 1 → B a b = 1)
    (g : GL (Fin 2) F) (hg : SourceKPIntegralMatrix ν g) (u : Fˣ) (hu : ν (u : F) = 1) :
    sourceKPCompactPhase ν B (g * sourceGL2Diagonal u) =
      sourceKPCompactPhase ν B g * sourceKPCompactPhase ν B (sourceGL2Diagonal u) *
        sourceKP2Multiplier B g (sourceGL2Diagonal u) := by
  let g' := g * sourceGL2Diagonal u
  have hg' := sourceKPIntegralMatrix_mul ν hg (sourceKPIntegralMatrix_diagonal ν u hu)
  have hD (hd : g 1 1 ≠ 0) (hd' : g' 1 1 ≠ 0) :
      Units.mk0 (g' 1 1) hd' / GeneralLinearGroup.det g' =
        (Units.mk0 (g 1 1) hd / GeneralLinearGroup.det g) / u := by
    have hE : Units.mk0 (g' 1 1) hd' = Units.mk0 (g 1 1) hd :=
      Units.ext (sourceGL2_right_diagonal_bottom_right g u)
    have hdet : GeneralLinearGroup.det g' = GeneralLinearGroup.det g * u := by
      change GeneralLinearGroup.det (g * sourceGL2Diagonal u) = _
      rw [map_mul, sourceGL2Diagonal_det]
    rw [hE, hdet]
    apply Additive.ofMul.injective
    simp only [ofMul_div, ofMul_mul]
    abel
  rw [sourceKPCompactPhase_rescale_right ν B hdiag hunit g g' hg hg' u hu
    (sourceGL2_right_diagonal_bottom_left g u) hD,
    sourceKPCompactPhase_zero_left ν B (sourceGL2Diagonal u) (by simp [sourceGL2Diagonal]),
    mul_one, sourceKP2Multiplier_compact_right_diagonal ν B hdiag hunit g hg u hu]
  split_ifs with hc
  · rw [sourceKPCompactPhase_zero_left ν B g hc, mul_one]
  · rfl

theorem sourceKPCompactPhase_right_scalar
    (hdiag : ∀ x, B x x = 1) (hcube : ∀ x y, B x y ^ 3 = 1)
    (hunit : ∀ a b : Fˣ, ν (a : F) = 1 → ν (b : F) = 1 → B a b = 1)
    (g : GL (Fin 2) F) (hg : SourceKPIntegralMatrix ν g) (u : Fˣ) (hu : ν (u : F) = 1) :
    sourceKPCompactPhase ν B (g * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPCompactPhase ν B g * sourceKPCompactPhase ν B (GeneralLinearGroup.scalar (Fin 2) u) *
        sourceKP2Multiplier B g (GeneralLinearGroup.scalar (Fin 2) u) := by
  let g' := g * GeneralLinearGroup.scalar (Fin 2) u
  have hg' := sourceKPIntegralMatrix_mul ν hg (sourceKPIntegralMatrix_scalar ν u hu)
  have hD (hd : g 1 1 ≠ 0) (hd' : g' 1 1 ≠ 0) :
      Units.mk0 (g' 1 1) hd' / GeneralLinearGroup.det g' =
        (Units.mk0 (g 1 1) hd / GeneralLinearGroup.det g) / u := by
    have hE : Units.mk0 (g' 1 1) hd' = Units.mk0 (g 1 1) hd * u :=
      Units.ext (sourceGL2_right_scalar_apply g u 1 1)
    have hdet : GeneralLinearGroup.det g' = GeneralLinearGroup.det g * u ^ 2 := by
      change GeneralLinearGroup.det (g * GeneralLinearGroup.scalar (Fin 2) u) = _
      rw [map_mul, sourceGL2_scalar_det]
    rw [hE, hdet]
    apply Additive.ofMul.injective
    simp only [ofMul_div, ofMul_mul, ofMul_pow]
    abel
  rw [sourceKPCompactPhase_rescale_right ν B hdiag hunit g g' hg hg' u hu
    (sourceGL2_right_scalar_apply g u 1 0) hD,
    sourceKPCompactPhase_zero_left ν B (GeneralLinearGroup.scalar (Fin 2) u)
      (by simp [GeneralLinearGroup.coe_scalar]),
    mul_one, sourceKP2Multiplier_compact_right_scalar ν B hdiag hcube hunit g hg u hu]
  split_ifs with hc
  · have hd := (sourceKPIntegralMatrix_bottom_unit ν hg).resolve_left (by
      rw [hc, map_zero]
      exact zero_ne_one)
    have hx : ν ((sourceKubotaX g : Fˣ) : F) = 1 := by rw [sourceKubotaX_val_right g hc, hd]
    rw [sourceKPCompactPhase_zero_left ν B g hc, hunit u _ hu hx, mul_one]
  · rfl

end
end ArtinMatthews
