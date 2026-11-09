module

public import ArtinMatthews.SourceKubotaMultipliers
public import Mathlib.Tactic.Abel


set_option backward.privateInPublic true
@[expose] public section

/-! Exact algebraic defect of the actual determinant-modified Kubota
formula. This expression is reduced to one Hilbert symbol before the
bottom-row and Steinberg analysis. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F : Type*} [Field F] {A : Type*} [CommGroup A]
    (B : Fˣ →* (Fˣ →* A))

theorem sourceKubotaSymbol_skew (hdiag : ∀ x, B x x = 1) (x y : Fˣ) :
    B y x = (B x y)⁻¹ := by
  have h := hdiag (x * y)
  simp only [map_mul, MonoidHom.mul_apply, hdiag, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_left h

private theorem sourceKubotaSymbol_defect (hdiag : ∀ x, B x x = 1)
    (a b c u v k d e f : Fˣ) :
    ((B (c / a) (c / (b * d)) * B d e ^ 2) *
        (B (v / c) (v / (k * (d * e))) * B (d * e) f ^ 2)) /
      ((B (v / a) (v / (u * d)) * B d (e * f) ^ 2) *
        (B (u / b) (u / (k * e)) * B e f ^ 2)) =
      B ((c * u) / (b * v)) ((a * e * k) / (b * v)) := by
  have hskew := sourceKubotaSymbol_skew B hdiag
  apply Additive.ofMul.injective
  simp only [map_div, map_mul, MonoidHom.div_apply, MonoidHom.mul_apply, hdiag,
    hskew a b, hskew a c, hskew a u, hskew a v, hskew b c, hskew b u, hskew b v, hskew u v,
    ofMul_div, ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
  abel

def sourceKP2Defect (g h k : GL (Fin 2) F) : A :=
  (sourceKP2Multiplier B g h * sourceKP2Multiplier B (g * h) k) /
    (sourceKP2Multiplier B g (h * k) * sourceKP2Multiplier B h k)

theorem sourceKP2Defect_formula (hdiag : ∀ x, B x x = 1) (g h k : GL (Fin 2) F) :
    sourceKP2Defect B g h k =
      B ((sourceKubotaX (g * h) * sourceKubotaX (h * k)) /
          (sourceKubotaX h * sourceKubotaX (g * h * k)))
        ((sourceKubotaX g * GeneralLinearGroup.det h * sourceKubotaX k) /
          (sourceKubotaX h * sourceKubotaX (g * h * k))) := by
  simpa only [sourceKP2Defect, sourceKP2Multiplier, map_mul, mul_assoc] using
    sourceKubotaSymbol_defect B hdiag
      (sourceKubotaX g) (sourceKubotaX h) (sourceKubotaX (g * h)) (sourceKubotaX (h * k))
      (sourceKubotaX (g * h * k)) (sourceKubotaX k) (GeneralLinearGroup.det g)
      (GeneralLinearGroup.det h) (GeneralLinearGroup.det k)

theorem sourceKP2Defect_eq_one_iff (g h k : GL (Fin 2) F) :
    sourceKP2Defect B g h k = 1 ↔
      sourceKP2Multiplier B g h * sourceKP2Multiplier B (g * h) k =
        sourceKP2Multiplier B g (h * k) * sourceKP2Multiplier B h k := div_eq_one

end
end ArtinMatthews
