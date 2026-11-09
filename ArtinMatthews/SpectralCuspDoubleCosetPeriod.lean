module

public import ArtinMatthews.KloostermanDoubleCoset
public import ArtinMatthews.SpectralGamma0CuspPeriod


set_option backward.privateInPublic true
@[expose] public section

/-! The arithmetic correspondence for the actual integral cusp translates.
Common-period N double cosets have diagonal residues modulo N*c, not c. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

theorem integerTranslation_eq_T_zpow (k : ℤ) :
    integerTranslation k = ModularGroup.T ^ k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [integerTranslation, ModularGroup.coe_T_zpow]

theorem integerTranslation_add (k l : ℤ) :
    integerTranslation (k + l) = integerTranslation k * integerTranslation l := by
  simp only [integerTranslation_eq_T_zpow, zpow_add]

theorem integerTranslation_neg (k : ℤ) :
    integerTranslation (-k) = (integerTranslation k)⁻¹ := by
  simp only [integerTranslation_eq_T_zpow, zpow_neg]

def gamma0CuspCorrespondence (N : ℕ) (r s : SL(2, ℤ)) : Set (SL(2, ℤ)) :=
  {M | s⁻¹ * M * r ∈ CongruenceSubgroup.Gamma0 N}

def gamma0CuspMatrixEquiv (N : ℕ) (r s : SL(2, ℤ)) :
    CongruenceSubgroup.Gamma0 N ≃ gamma0CuspCorrespondence N r s where
  toFun γ := ⟨s * (γ : SL(2, ℤ)) * r⁻¹, by
    change s⁻¹ * (s * (γ : SL(2, ℤ)) * r⁻¹) * r ∈ CongruenceSubgroup.Gamma0 N
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using γ.property⟩
  invFun M := ⟨s⁻¹ * M.val * r, M.property⟩
  left_inv γ := by apply Subtype.ext; dsimp; group
  right_inv M := by apply Subtype.ext; dsimp; group

theorem gamma0CuspMatrixEquiv_apply (N : ℕ) (r s : SL(2, ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) :
    (gamma0CuspMatrixEquiv N r s γ).val = s * (γ : SL(2, ℤ)) * r⁻¹ := rfl

theorem gamma0_conjugate_period_translation_mem (N : ℕ) (r : SL(2, ℤ)) (k : ℤ) :
    r⁻¹ * integerTranslation ((N : ℤ) * k) * r ∈ CongruenceSubgroup.Gamma0 N := by
  rw [integerTranslation_eq_T_zpow]
  have hT : ModularGroup.T ^ ((N : ℤ) * k) ∈ CongruenceSubgroup.Gamma N := by
    exact CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) ((N : ℤ) * k)
      (dvd_mul_right _ _)
  have hconj : r⁻¹ * ModularGroup.T ^ ((N : ℤ) * k) * r ∈ CongruenceSubgroup.Gamma N := by
    rw [CongruenceSubgroup.Gamma_mem'] at hT ⊢
    simp only [map_mul, map_inv, hT, mul_one, inv_mul_cancel]
  exact CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hconj).2.2.1

theorem gamma0CuspCorrespondence_period_translate (N : ℕ) (r s : SL(2, ℤ))
    (M : SL(2, ℤ)) (hM : M ∈ gamma0CuspCorrespondence N r s) (l k : ℤ) :
    integerTranslation ((N : ℤ) * l) * M * integerTranslation ((N : ℤ) * k) ∈
      gamma0CuspCorrespondence N r s := by
  have h := (CongruenceSubgroup.Gamma0 N).mul_mem
    ((CongruenceSubgroup.Gamma0 N).mul_mem
      (gamma0_conjugate_period_translation_mem N s l) hM)
    (gamma0_conjugate_period_translation_mem N r k)
  change s⁻¹ * (integerTranslation ((N : ℤ) * l) * M * integerTranslation ((N : ℤ) * k)) * r ∈
    CongruenceSubgroup.Gamma0 N
  convert h using 1
  group

theorem integerTranslation_period_double_coset_iff (N : ℕ) [NeZero N]
    {c : ℤ} (hc : c ≠ 0) (M R : SL(2, ℤ)) (hM : M 1 0 = c) (hR : R 1 0 = c) :
    (Int.ModEq ((N : ℤ) * c) (M 0 0) (R 0 0) ∧
      Int.ModEq ((N : ℤ) * c) (M 1 1) (R 1 1)) ↔
      ∃ l k : ℤ, R = integerTranslation ((N : ℤ) * l) * M * integerTranslation ((N : ℤ) * k) := by
  constructor
  · rintro ⟨hA,hD⟩
    obtain ⟨l,hl⟩ := hA.dvd
    obtain ⟨k,hk⟩ := hD.dvd
    let T := integerTranslation ((N : ℤ) * l) * M * integerTranslation ((N : ℤ) * k)
    obtain ⟨hTA,hTC,hTD⟩ := integerTranslation_entries ((N : ℤ) * l) ((N : ℤ) * k) M
    have hA' : T 0 0 = R 0 0 := by rw [hTA,hM]; nlinarith
    have hC' : T 1 0 = c := hTC.trans hM
    have hD' : T 1 1 = R 1 1 := by rw [hTD,hM]; nlinarith
    have hB' : T 0 1 = R 0 1 := by
      have ht := T.prop
      have hr := R.prop
      rw [Matrix.det_fin_two,hA',hC',hD'] at ht
      rw [Matrix.det_fin_two,hR] at hr
      apply mul_right_cancel₀ hc
      nlinarith
    refine ⟨l,k,?_⟩
    change R = T
    ext i j
    fin_cases i <;> fin_cases j
    · exact hA'.symm
    · exact hB'.symm
    · exact hR.trans hC'.symm
    · exact hD'.symm
  · rintro ⟨l,k,rfl⟩
    obtain ⟨hA,_hC,hD⟩ := integerTranslation_entries ((N : ℤ) * l) ((N : ℤ) * k) M
    constructor
    · apply Int.modEq_iff_dvd.mpr
      refine ⟨l,?_⟩
      rw [hA,hM]
      ring
    · apply Int.modEq_iff_dvd.mpr
      refine ⟨k,?_⟩
      rw [hD,hM]
      ring

end ArtinMatthews
