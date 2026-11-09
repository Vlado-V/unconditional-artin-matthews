module

public import ArtinMatthews.SpectralCuspWidthNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized real matrices and phases.  The normalized lower
entry is c*sqrt(w_r)*sqrt(w_s), and is not silently identified with c. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0TrueWidthMatrix (N : ℕ) [NeZero N] (r s M : SL(2, ℤ)) : SL(2, ℝ) :=
  (cuspWidthDilation (gamma0CuspTrueWidth N s : ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N s))⁻¹ * atkinRealMap M *
      cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ)
        (by exact_mod_cast gamma0CuspTrueWidth_pos N r)

theorem gamma0TrueWidthMatrix_correspondence (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N) :
    gamma0TrueWidthMatrix N r s (s * γ.val * r⁻¹) =
      (gamma0TrueCuspScaling N s)⁻¹ * atkinRealMap γ.val * gamma0TrueCuspScaling N r := by
  unfold gamma0TrueWidthMatrix gamma0TrueCuspScaling
  rw [map_mul,map_mul,map_inv]
  group

set_option backward.isDefEq.respectTransparency false in
theorem gamma0TrueWidthMatrix_entries (N : ℕ) [NeZero N] (r s M : SL(2, ℤ)) :
    gamma0TrueWidthMatrix N r s M 0 0 =
      (M 0 0 : ℝ)*Real.sqrt (gamma0CuspTrueWidth N r : ℝ) /
        Real.sqrt (gamma0CuspTrueWidth N s : ℝ) ∧
    gamma0TrueWidthMatrix N r s M 1 0 =
      (M 1 0 : ℝ)*Real.sqrt (gamma0CuspTrueWidth N r : ℝ)*
        Real.sqrt (gamma0CuspTrueWidth N s : ℝ) ∧
    gamma0TrueWidthMatrix N r s M 1 1 =
      (M 1 1 : ℝ)*Real.sqrt (gamma0CuspTrueWidth N s : ℝ) /
        Real.sqrt (gamma0CuspTrueWidth N r : ℝ) := by
  simp [gamma0TrueWidthMatrix,cuspWidthDilation,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.mul_apply,
    Matrix.vecMul,dotProduct,Fin.sum_univ_two,atkinRealMap,div_eq_mul_inv,mul_comm,mul_left_comm]

def gamma0TrueWidthModulus (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (c : ℝ) : ℝ :=
  c * Real.sqrt (gamma0CuspTrueWidth N r : ℝ) * Real.sqrt (gamma0CuspTrueWidth N s : ℝ)

theorem gamma0TrueWidthModulus_pos (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) {c : ℝ} (hc : 0 < c) : 0 < gamma0TrueWidthModulus N r s c := by
  exact mul_pos (mul_pos hc (Real.sqrt_pos.mpr (by exact_mod_cast gamma0CuspTrueWidth_pos N r)))
    (Real.sqrt_pos.mpr (by exact_mod_cast gamma0CuspTrueWidth_pos N s))

theorem gamma0TrueWidthMatrix_lower (N : ℕ) [NeZero N]
    (r s M : SL(2, ℤ)) (c : ℤ) (hM : M 1 0 = c) :
    gamma0TrueWidthMatrix N r s M 1 0 = gamma0TrueWidthModulus N r s c := by
  rw [(gamma0TrueWidthMatrix_entries N r s M).2.1,hM]
  rfl

def cuspTrueWidthGeometricPhase (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n c : ℤ) (M : SL(2, ℤ)) : ℂ :=
  atkinPhase (((m : ℝ)*(M 1 1 : ℝ))/((gamma0CuspTrueWidth N r : ℝ)*c) +
    ((n : ℝ)*(M 0 0 : ℝ))/((gamma0CuspTrueWidth N s : ℝ)*c))

theorem cuspGeometricPhase_trueWidth (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n c : ℤ) (hc : c ≠ 0) (M : SL(2, ℤ)) :
    cuspGeometricPhase N ((gamma0CuspFrequencyStep N r : ℤ)*m)
      ((gamma0CuspFrequencyStep N s : ℤ)*n) c M =
        cuspTrueWidthGeometricPhase N r s m n c M := by
  have hr : (gamma0CuspTrueWidth N r : ℝ)*gamma0CuspFrequencyStep N r = N := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hs : (gamma0CuspTrueWidth N s : ℝ)*gamma0CuspFrequencyStep N s = N := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N s
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hwr : (gamma0CuspTrueWidth N r : ℝ) ≠ 0 := by
    exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne'
  have hws : (gamma0CuspTrueWidth N s : ℝ) ≠ 0 := by
    exact_mod_cast (gamma0CuspTrueWidth_pos N s).ne'
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  unfold cuspGeometricPhase cuspTrueWidthGeometricPhase
  congr 1
  push_cast
  field_simp [hN,hwr,hws,hcR]
  linear_combination (m : ℝ)*(M 1 1 : ℝ)*(gamma0CuspTrueWidth N s : ℝ)*hr +
    (n : ℝ)*(M 0 0 : ℝ)*(gamma0CuspTrueWidth N r : ℝ)*hs

theorem cuspTrueWidthGeometricPhase_normalized (N : ℕ) [NeZero N]
    (r s M : SL(2, ℤ)) (m n c : ℤ) (hc : c ≠ 0) (hM : M 1 0 = c) :
    cuspTrueWidthGeometricPhase N r s m n c M =
      atkinPhase (((m : ℝ)*gamma0TrueWidthMatrix N r s M 1 1 +
        (n : ℝ)*gamma0TrueWidthMatrix N r s M 0 0) /
          gamma0TrueWidthMatrix N r s M 1 0) := by
  have hwr : 0 < (gamma0CuspTrueWidth N r : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N r
  have hws : 0 < (gamma0CuspTrueWidth N s : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N s
  have hsr := (Real.sqrt_pos.mpr hwr).ne'
  have hss := (Real.sqrt_pos.mpr hws).ne'
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  obtain ⟨hA,hC,hD⟩ := gamma0TrueWidthMatrix_entries N r s M
  unfold cuspTrueWidthGeometricPhase
  rw [hA,hC,hD,hM]
  congr 1
  field_simp [hwr.ne',hws.ne',hsr,hss,hcR]
  rw [Real.sq_sqrt hwr.le,Real.sq_sqrt hws.le]
  ring

theorem cuspTrueWidthGeometricPhase_translate (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n c : ℤ) (hc : c ≠ 0) (M : SL(2, ℤ))
    (hM : M 1 0 = c) (l k : ℤ) :
    cuspTrueWidthGeometricPhase N r s m n c
      (integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*l) * M *
        integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) =
      cuspTrueWidthGeometricPhase N r s m n c M := by
  have hwr : (gamma0CuspTrueWidth N r : ℝ) ≠ 0 := by
    exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne'
  have hws : (gamma0CuspTrueWidth N s : ℝ) ≠ 0 := by
    exact_mod_cast (gamma0CuspTrueWidth_pos N s).ne'
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  obtain ⟨hA,_,hD⟩ := integerTranslation_entries
    ((gamma0CuspTrueWidth N s : ℤ)*l) ((gamma0CuspTrueWidth N r : ℤ)*k) M
  have he :
      ((m : ℝ)*((integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*l) * M *
        integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) 1 1 : ℝ)) /
          ((gamma0CuspTrueWidth N r : ℝ)*c) +
      ((n : ℝ)*((integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*l) * M *
        integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) 0 0 : ℝ)) /
          ((gamma0CuspTrueWidth N s : ℝ)*c) =
      ((m : ℝ)*(M 1 1 : ℝ))/((gamma0CuspTrueWidth N r : ℝ)*c) +
      ((n : ℝ)*(M 0 0 : ℝ))/((gamma0CuspTrueWidth N s : ℝ)*c) +
      ((m*k+n*l : ℤ) : ℝ) := by
    rw [hA,hD,hM]
    push_cast
    field_simp [hwr,hws,hcR]
    ring
  unfold cuspTrueWidthGeometricPhase
  rw [he,atkinPhase_add,atkinPhase_int,mul_one]

end ArtinMatthews
