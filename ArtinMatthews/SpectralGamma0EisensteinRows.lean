module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


set_option backward.privateInPublic true
@[expose] public section

/-! Actual bottom rows of Γ₀(N), before any spectral-resolution claim. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0EisensteinRow (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) : Fin 2 → ℤ :=
  (g : SL(2,ℤ)) 1

theorem gamma0EisensteinRow_mul (N : ℕ) (g h : CongruenceSubgroup.Gamma0 N) :
    gamma0EisensteinRow N (g*h) = Matrix.vecMul (gamma0EisensteinRow N g) (h : SL(2,ℤ)) := by
  funext j
  simp only [gamma0EisensteinRow,Subgroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Matrix.vecMul,dotProduct]

theorem gamma0EisensteinRow_ne_zero (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    gamma0EisensteinRow N g ≠ 0 := by
  intro h
  have hc : (g : SL(2,ℤ)) 1 0 = 0 := congrFun h 0
  have hd : (g : SL(2,ℤ)) 1 1 = 0 := congrFun h 1
  have he : (g : SL(2,ℤ)) 0 0 * (g : SL(2,ℤ)) 1 1 -
      (g : SL(2,ℤ)) 0 1 * (g : SL(2,ℤ)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (g : SL(2,ℤ)).property
  simp only [hc,hd,mul_zero,sub_zero] at he
  exact zero_ne_one he

abbrev Gamma0EisensteinRows (N : ℕ) := {v : Fin 2 → ℤ // v ∈ Set.range (gamma0EisensteinRow N)}

def gamma0EisensteinRowRepresentative (N : ℕ) (v : Gamma0EisensteinRows N) :
    CongruenceSubgroup.Gamma0 N := v.property.choose

theorem gamma0EisensteinRowRepresentative_spec (N : ℕ) (v : Gamma0EisensteinRows N) :
    gamma0EisensteinRow N (gamma0EisensteinRowRepresentative N v) = v.val :=
  v.property.choose_spec

theorem gamma0EisensteinRows_ne_zero (N : ℕ) (v : Gamma0EisensteinRows N) : v.val ≠ 0 := by
  rw [← gamma0EisensteinRowRepresentative_spec N v]
  exact gamma0EisensteinRow_ne_zero N _

def gamma0EisensteinRowRight (N : ℕ) (g : CongruenceSubgroup.Gamma0 N)
    (v : Gamma0EisensteinRows N) : Gamma0EisensteinRows N :=
  ⟨Matrix.vecMul v.val (g : SL(2,ℤ)), by
    refine ⟨gamma0EisensteinRowRepresentative N v * g,?_⟩
    rw [gamma0EisensteinRow_mul,gamma0EisensteinRowRepresentative_spec]⟩

def gamma0EisensteinRowEquiv (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    Gamma0EisensteinRows N ≃ Gamma0EisensteinRows N where
  toFun := gamma0EisensteinRowRight N g
  invFun := gamma0EisensteinRowRight N g⁻¹
  left_inv v := by
    apply Subtype.ext
    change Matrix.vecMul (Matrix.vecMul v.val ((g : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      (((g⁻¹ : CongruenceSubgroup.Gamma0 N) : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = v.val
    rw [Matrix.vecMul_vecMul]
    change Matrix.vecMul v.val (((g : SL(2,ℤ))*(g : SL(2,ℤ))⁻¹ : SL(2,ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) = v.val
    rw [mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.vecMul_one]
  right_inv v := by
    apply Subtype.ext
    change Matrix.vecMul (Matrix.vecMul v.val
      (((g⁻¹ : CongruenceSubgroup.Gamma0 N) : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      ((g : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = v.val
    rw [Matrix.vecMul_vecMul]
    change Matrix.vecMul v.val (((g : SL(2,ℤ))⁻¹*(g : SL(2,ℤ)) : SL(2,ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) = v.val
    rw [inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.vecMul_one]

def gamma0EisensteinHeight (N : ℕ) (v : Gamma0EisensteinRows N) (z : UpperHalfPlane) : ℝ :=
  ((gamma0EisensteinRowRepresentative N v : SL(2,ℤ)) • z).im

theorem gamma0EisensteinHeight_pos (N : ℕ) (v : Gamma0EisensteinRows N) (z : UpperHalfPlane) :
    0 < gamma0EisensteinHeight N v z := UpperHalfPlane.im_pos _

theorem gamma0EisensteinHeight_row (N : ℕ) (v : Gamma0EisensteinRows N) (z : UpperHalfPlane) :
    gamma0EisensteinHeight N v z = z.im / ‖(v.val 0 : ℂ)*z + v.val 1‖^2 := by
  unfold gamma0EisensteinHeight
  rw [ModularGroup.im_smul_eq_div_normSq,ModularGroup.denom_apply,Complex.normSq_eq_norm_sq]
  have h := gamma0EisensteinRowRepresentative_spec N v
  rw [show (gamma0EisensteinRowRepresentative N v : SL(2,ℤ)) 1 0 = v.val 0 from congrFun h 0,
    show (gamma0EisensteinRowRepresentative N v : SL(2,ℤ)) 1 1 = v.val 1 from congrFun h 1]

theorem gamma0EisensteinHeight_of_row (N : ℕ) (v : Gamma0EisensteinRows N)
    (g : CongruenceSubgroup.Gamma0 N) (hg : gamma0EisensteinRow N g = v.val) (z : UpperHalfPlane) :
    gamma0EisensteinHeight N v z = ((g : SL(2,ℤ)) • z).im := by
  rw [gamma0EisensteinHeight_row,ModularGroup.im_smul_eq_div_normSq,
    ModularGroup.denom_apply,Complex.normSq_eq_norm_sq]
  rw [show (g : SL(2,ℤ)) 1 0 = v.val 0 from congrFun hg 0,
    show (g : SL(2,ℤ)) 1 1 = v.val 1 from congrFun hg 1]

theorem gamma0EisensteinHeight_right (N : ℕ) (v : Gamma0EisensteinRows N)
    (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0EisensteinHeight N (gamma0EisensteinRowEquiv N g v) z =
      gamma0EisensteinHeight N v ((g : SL(2,ℤ)) • z) := by
  rw [gamma0EisensteinHeight_of_row N _ (gamma0EisensteinRowRepresentative N v * g)
    (by rw [gamma0EisensteinRow_mul,gamma0EisensteinRowRepresentative_spec]; rfl)]
  simp only [Subgroup.coe_mul,mul_smul,gamma0EisensteinHeight]

end ArtinMatthews
