module

public import ArtinMatthews.AtkinLehnerMixedResidues


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit lower-triangular scaling phase in the mixed-cusp kernel. -/
namespace ArtinMatthews

open Matrix
open scoped BigOperators

def realTranslation (x : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![1,x;0,1],by simp [Matrix.det_fin_two]⟩

noncomputable def lowerTriScaling {r : ℕ} (hr : 0 < r) (s : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![Real.sqrt (r : ℝ),0;(s : ℝ)*Real.sqrt (r : ℝ),1/Real.sqrt (r : ℝ)],by
    have ht : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
    simp [Matrix.det_fin_two,ht]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The normalized Atkin-Lehner scaling differs from the actual source
lower-triangular scaling by the stated right translation. -/
theorem atkinScaling_eq_lowerTri_translation {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    atkinScaling hr hab = lowerTriScaling hr s * realTranslation ((b : ℝ)/(r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have ht : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hrR).ne'
  have hsq := Real.sq_sqrt hrR.le
  have habR : (r : ℝ)*(a : ℝ)-(s : ℝ)*(b : ℝ) = 1 := by exact_mod_cast hab
  ext i j
  fin_cases i <;> fin_cases j
  · simp [atkinScaling,atkinScalingMatrix,atkinNumerator,lowerTriScaling,realTranslation,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    field_simp [ht]
    nlinarith
  · simp [atkinScaling,atkinScalingMatrix,atkinNumerator,lowerTriScaling,realTranslation,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    field_simp [ht,hrR.ne']
    linear_combination -(b : ℝ)*hsq
  · simp [atkinScaling,atkinScalingMatrix,atkinNumerator,lowerTriScaling,realTranslation,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    field_simp [ht]
    linear_combination -(s : ℝ)*hsq
  · simp [atkinScaling,atkinScalingMatrix,atkinNumerator,lowerTriScaling,realTranslation,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    field_simp [ht,hrR.ne']
    linear_combination (r : ℝ)*habR-(s : ℝ)*(b : ℝ)*hsq

set_option backward.isDefEq.respectTransparency false in
theorem realTranslation_mul (x y : ℝ) : realTranslation x * realTranslation y = realTranslation (x+y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realTranslation,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,
      Fin.sum_univ_two,add_comm]

theorem lowerTriScaling_eq_atkin_translation {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    lowerTriScaling hr s = atkinScaling hr hab * realTranslation (-(b : ℝ)/(r : ℝ)) := by
  rw [atkinScaling_eq_lowerTri_translation hr hab,mul_assoc,realTranslation_mul]
  have he : (b : ℝ)/(r : ℝ)+(-(b : ℝ)/(r : ℝ)) = 0 := by ring
  rw [he]
  have hzero : realTranslation 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hzero,mul_one]

set_option backward.isDefEq.respectTransparency false in
theorem realTranslation_right_entries (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : ℝ) :
    (γ*realTranslation x) 0 0 = γ 0 0 ∧
    (γ*realTranslation x) 1 0 = γ 1 0 ∧
    (γ*realTranslation x) 1 1 = γ 1 1+γ 1 0*x := by
  simp [realTranslation,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,
    Fin.sum_univ_two,add_comm]

/-- The source lower-triangular scaling has exactly the same allowable moduli. -/
theorem lowerTriMixedAllowed_iff {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (γc : ℝ) :
    (0 < γc ∧ ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ ∈ CongruenceSubgroup.Gamma0 (r*s) ∧
      (atkinRealMap γ*lowerTriScaling hr s) 1 0 = γc) ↔ atkinMixedAllowed hr hab γc := by
  have he (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      (atkinRealMap γ*lowerTriScaling hr s) 1 0 = (atkinRealMap γ*atkinScaling hr hab) 1 0 := by
    rw [lowerTriScaling_eq_atkin_translation hr hab,← mul_assoc]
    exact (realTranslation_right_entries _ _).2.1
  simp only [atkinMixedAllowed,he]

/-- The actual lower-triangular matrix phase has the required explicit shift,
for every integer sign of either additive frequency. -/
theorem lowerTriMixed_matrix_phase {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hc : (atkinRealMap γ*atkinScaling hr hab) 1 0 ≠ 0) (m n : ℝ) :
    (m*(atkinRealMap γ*lowerTriScaling hr s) 0 0+
      n*(atkinRealMap γ*lowerTriScaling hr s) 1 1)/(atkinRealMap γ*lowerTriScaling hr s) 1 0 =
    (m*(atkinRealMap γ*atkinScaling hr hab) 0 0+
      n*(atkinRealMap γ*atkinScaling hr hab) 1 1)/(atkinRealMap γ*atkinScaling hr hab) 1 0-
      n*(b : ℝ)/(r : ℝ) := by
  rw [lowerTriScaling_eq_atkin_translation hr hab,← mul_assoc]
  obtain ⟨hA,hC,hD⟩ := realTranslation_right_entries
    (atkinRealMap γ*atkinScaling hr hab) (-(b : ℝ)/(r : ℝ))
  rw [hA,hC,hD]
  field_simp [hc]
  ring

/-- The integer `-b` is precisely an inverse of `s` modulo `r`; this identifies
the phase with the inverse-s phase written in ABL's formula. -/
theorem atkinMixed_inverse_s {r s : ℕ} {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) : Int.ModEq (r : ℤ) ((s : ℤ)*(-b)) 1 := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨a,by linear_combination -hab⟩

noncomputable def atkinPhase (x : ℝ) : ℂ := Complex.exp (2*Real.pi*Complex.I*(x : ℂ))

theorem atkinPhase_add (x y : ℝ) : atkinPhase (x+y) = atkinPhase x * atkinPhase y := by
  unfold atkinPhase
  push_cast
  rw [show 2*(Real.pi : ℂ)*Complex.I*((x : ℂ)+(y : ℂ)) =
      2*(Real.pi : ℂ)*Complex.I*(x : ℂ)+2*(Real.pi : ℂ)*Complex.I*(y : ℂ) by ring,
    Complex.exp_add]

theorem stdAddChar_eq_atkinPhase {q : ℕ} [NeZero q] (v : ℤ) :
    ZMod.stdAddChar (v : ZMod q) = atkinPhase ((v : ℝ)/(q : ℝ)) := by
  rw [ZMod.stdAddChar_coe]
  unfold atkinPhase
  push_cast
  congr 1
  ring

/-- The source scaling phase is retained in every finite residue term. -/
noncomputable def lowerTriMixedResidueSum {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero (s*c)] (m n : ℤ) : ℂ :=
  ∑ ad ∈ atkinMixedResiduePairs hr hab c,
    atkinPhase (((m : ℝ)*(ad.1.val : ℝ)+(n : ℝ)*(ad.2.val : ℝ))/((s*c : ℕ) : ℝ)-
      (n : ℝ)*(b : ℝ)/(r : ℝ))

/-- The explicit phase and the ordinary inverse-r sum in ABL section 6. -/
theorem lowerTriMixedResidueSum_eq_ordinary {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero (s*c)]
    (hrq : r.Coprime (s*c)) (m n : ℤ) :
    lowerTriMixedResidueSum hr hab c m n =
      atkinPhase (-(n : ℝ)*(b : ℝ)/(r : ℝ)) *
        OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar
          ((m : ZMod (s*c))*(↑(ZMod.unitOfCoprime r hrq)⁻¹ : ZMod (s*c))) (n : ZMod (s*c)) := by
  classical
  have hbase (ad : ZMod (s*c) × ZMod (s*c)) :
      atkinPhase (((m : ℝ)*(ad.1.val : ℝ)+(n : ℝ)*(ad.2.val : ℝ))/((s*c : ℕ) : ℝ)) =
        ZMod.stdAddChar ((m : ZMod (s*c))*ad.1+(n : ZMod (s*c))*ad.2) := by
    let v : ℤ := m*(ad.1.val : ℤ)+n*(ad.2.val : ℤ)
    have hv : (v : ZMod (s*c)) = (m : ZMod (s*c))*ad.1+(n : ZMod (s*c))*ad.2 := by
      dsimp [v]
      push_cast
      simp
    rw [← hv,stdAddChar_eq_atkinPhase]
    congr 1
    dsimp [v]
    push_cast
    rfl
  unfold lowerTriMixedResidueSum
  simp_rw [sub_eq_add_neg,atkinPhase_add,hbase]
  rw [← Finset.sum_mul]
  change atkinMixedResidueSum hr hab c (m : ZMod (s*c)) (n : ZMod (s*c)) * _ = _
  rw [atkinMixedResidueSum_eq_ordinary hr hab c hrq]
  have he : -((n : ℝ)*(b : ℝ)/(r : ℝ)) = -(n : ℝ)*(b : ℝ)/(r : ℝ) := by ring
  rw [he,mul_comm]

end ArtinMatthews
