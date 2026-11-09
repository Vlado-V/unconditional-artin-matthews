module

public import ArtinMatthews.SourceKubotaDefect
public import ArtinMatthews.SourceFiniteKPMultipliers


set_option backward.privateInPublic true
@[expose] public section

/-! The full ordinary scalar subgroup, rather than just the two
specific scalar factors in the Bruhat relations. The determinant
twist is exactly what makes the ordinary scalar section central. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F : Type*} [Field F] {A : Type*} [CommGroup A]
    (B : Fˣ →* (Fˣ →* A))

theorem sourceKubotaX_scalar_mul (g : GL (Fin 2) F) (u : Fˣ) :
    sourceKubotaX (GeneralLinearGroup.scalar (Fin 2) u * g) = sourceKubotaX g * u := by
  rw [GeneralLinearGroup.scalar_commute u g, sourceKubotaX_mul_scalar]

theorem sourceGL2_scalar_det (u : Fˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) u) = u ^ 2 := by
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem sourceKubotaSymbol_fourth (hcube : ∀ a b, B a b ^ 3 = 1) (a b : Fˣ) :
    B a b ^ (2 * 2 : ℕ) = B a b := by
  change B a b ^ (3 + 1 : ℕ) = _
  rw [pow_succ, hcube, one_mul]

theorem sourceKP2Multiplier_scalar_left (hdiag : ∀ x, B x x = 1)
    (hcube : ∀ a b, B a b ^ 3 = 1) (g : GL (Fin 2) F) (u : Fˣ) :
    sourceKP2Multiplier B (GeneralLinearGroup.scalar (Fin 2) u) g =
      B u (sourceKubotaX g * GeneralLinearGroup.det g) := by
  have h₁ : (sourceKubotaX g * u) / u = sourceKubotaX g := by simp
  have h₂ : (sourceKubotaX g * u) / (sourceKubotaX g * u ^ 2) = u⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_pow]
    abel
  rw [sourceKP2Multiplier, sourceKubotaX_scalar_mul, sourceKubotaX_scalar, sourceGL2_scalar_det, h₁, h₂]
  simp only [map_inv, map_pow, MonoidHom.pow_apply]
  rw [sourceKubotaSymbol_skew B hdiag u (sourceKubotaX g), inv_inv, ← pow_mul,
    sourceKubotaSymbol_fourth B hcube, map_mul]

theorem sourceKP2Multiplier_scalar_right (hdiag : ∀ x, B x x = 1)
    (hcube : ∀ a b, B a b ^ 3 = 1) (g : GL (Fin 2) F) (u : Fˣ) :
    sourceKP2Multiplier B g (GeneralLinearGroup.scalar (Fin 2) u) =
      B u (sourceKubotaX g * GeneralLinearGroup.det g) := by
  have h₁ : (sourceKubotaX g * u) / sourceKubotaX g = u := by
    rw [mul_comm, mul_div_cancel_right]
  have h₂ : (sourceKubotaX g * u) / (u * GeneralLinearGroup.det g) =
      sourceKubotaX g / GeneralLinearGroup.det g := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  have h₃ : (B u (GeneralLinearGroup.det g))⁻¹ * (B u (GeneralLinearGroup.det g))⁻¹ =
      B u (GeneralLinearGroup.det g) := by
    have hz : B u (GeneralLinearGroup.det g) ^ 2 * B u (GeneralLinearGroup.det g) = 1 := by
      rw [← pow_succ]
      exact hcube _ _
    rw [← pow_two, inv_pow, eq_inv_of_mul_eq_one_left hz, inv_inv]
  rw [sourceKP2Multiplier, sourceKubotaX_mul_scalar, sourceKubotaX_scalar, sourceGL2_scalar_det, h₁, h₂]
  simp only [map_div, map_pow]
  rw [← pow_mul, sourceKubotaSymbol_fourth B hcube, sourceKubotaSymbol_skew B hdiag u (GeneralLinearGroup.det g),
    div_eq_mul_inv, mul_assoc, h₃, map_mul]

theorem sourceKP2Multiplier_scalar_pair (hdiag : ∀ x, B x x = 1)
    (hcube : ∀ a b, B a b ^ 3 = 1) (u v : Fˣ) :
    sourceKP2Multiplier B (GeneralLinearGroup.scalar (Fin 2) u) (GeneralLinearGroup.scalar (Fin 2) v) = 1 := by
  rw [sourceKP2Multiplier_scalar_left B hdiag hcube, sourceKubotaX_scalar, sourceGL2_scalar_det,
    mul_comm v, ← pow_succ, map_pow]
  exact hcube _ _

open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceFiniteKP2Multiplier_scalar_comm (g : GL (Fin 2) (P.adicCompletion K))
    (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2Multiplier K hζ P (GeneralLinearGroup.scalar (Fin 2) u) g =
      sourceFiniteKP2Multiplier K hζ P g (GeneralLinearGroup.scalar (Fin 2) u) := by
  let B := sourceFiniteKPHilbert K hζ P
  exact (sourceKP2Multiplier_scalar_left B (sourceFiniteKPHilbert_diag K hζ P)
    (fun a b => sourceCubicRoot_cube _ (B a b)) g u).trans
      (sourceKP2Multiplier_scalar_right B (sourceFiniteKPHilbert_diag K hζ P)
        (fun a b => sourceCubicRoot_cube _ (B a b)) g u).symm

theorem sourceFiniteKP2Multiplier_scalar_pair (u v : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2Multiplier K hζ P (GeneralLinearGroup.scalar (Fin 2) u)
      (GeneralLinearGroup.scalar (Fin 2) v) = 1 :=
  sourceKP2Multiplier_scalar_pair (sourceFiniteKPHilbert K hζ P) (sourceFiniteKPHilbert_diag K hζ P)
    (fun a b => sourceCubicRoot_cube _ (sourceFiniteKPHilbert K hζ P a b)) u v

end
end ArtinMatthews
