module

public import ArtinMatthews.SpectralCuspEisensteinZeroRows


set_option backward.privateInPublic true
@[expose] public section

/-! The actual zero-lower-entry cusp equivalence preserves the genuine least
positive period. Thus the leading normalized constant is exactly one. -/
noncomputable section
open Matrix
open scoped MatrixGroups
namespace ArtinMatthews

theorem specialLinear_upper_commutes_translation (M : SL(2,ℤ)) (hM : M 1 0=0) (k : ℤ) :
    integerTranslation k*M=M*integerTranslation k := by
  have hu := SpecialLinearGroup.isCoprime_row M 1
  rw [hM,isCoprime_zero_left] at hu
  have hdet : M 0 0*M 1 1=1 := by
    simpa only [Matrix.det_fin_two,hM,mul_zero,sub_zero] using M.property
  rcases Int.isUnit_iff.mp hu with hd | hd
  all_goals
    have ha : M 0 0=M 1 1 := by
      apply mul_right_cancel₀ (show M 1 1 ≠ 0 by rw [hd]; norm_num)
      rw [hdet,hd]
      norm_num
    ext i j
    change (∑ l : Fin 2, (integerTranslation k) i l*M l j)=
      ∑ l : Fin 2, M i l*(integerTranslation k) l j
    fin_cases i <;> fin_cases j
    all_goals simp [Fin.sum_univ_two,integerTranslation,hM,ha,hd,add_comm]

private theorem subgroup_conjugation_mem_iff {G : Type*} [Group G]
    (H : Subgroup G) (g : G) (hg : g ∈ H) (x : G) :
    g⁻¹*x*g ∈ H ↔ x ∈ H := by
  constructor
  · intro h
    have hh := H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
    convert hh using 1; group
  · intro h
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg

theorem gamma0EisensteinCuspsEquivalent_period_iff (N : ℕ) (r a : SL(2,ℤ))
    (h : gamma0EisensteinCuspsEquivalent N r a) (k : ℤ) :
    a⁻¹*integerTranslation k*a ∈ CongruenceSubgroup.Gamma0 N ↔
      r⁻¹*integerTranslation k*r ∈ CongruenceSubgroup.Gamma0 N := by
  obtain ⟨M,hM⟩ := (gamma0EisensteinCuspsEquivalent_iff N r a).mp h
  let g : SL(2,ℤ) := a⁻¹*M.val*r
  have hg : g ∈ CongruenceSubgroup.Gamma0 N := M.property
  have hcomm := specialLinear_upper_commutes_translation M.val hM k
  have hconj : M.val⁻¹*integerTranslation k*M.val=integerTranslation k := by
    rw [mul_assoc,hcomm]
    group
  have he : g⁻¹*(a⁻¹*integerTranslation k*a)*g=r⁻¹*integerTranslation k*r := by
    calc
      _=r⁻¹*(M.val⁻¹*integerTranslation k*M.val)*r := by dsimp [g]; group
      _=_ := by rw [hconj]
  rw [← he]
  exact (subgroup_conjugation_mem_iff _ g hg _).symm

theorem gamma0EisensteinCuspsEquivalent_width (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (h : gamma0EisensteinCuspsEquivalent N r a) :
    gamma0CuspTrueWidth N r=gamma0CuspTrueWidth N a := by
  apply Nat.dvd_antisymm
  · have hp := (gamma0CuspTrueWidth_translation_iff N a (gamma0CuspTrueWidth N a:ℤ)).mpr dvd_rfl
    have hr := (gamma0EisensteinCuspsEquivalent_period_iff N r a h _).mp hp
    have hd := (gamma0CuspTrueWidth_translation_iff N r (gamma0CuspTrueWidth N a:ℤ)).mp hr
    exact_mod_cast hd
  · have hp := (gamma0CuspTrueWidth_translation_iff N r (gamma0CuspTrueWidth N r:ℤ)).mpr dvd_rfl
    have ha := (gamma0EisensteinCuspsEquivalent_period_iff N r a h _).mpr hp
    have hd := (gamma0CuspTrueWidth_translation_iff N a (gamma0CuspTrueWidth N r:ℤ)).mp ha
    exact_mod_cast hd

def gamma0CuspEisensteinIndicator (N : ℕ) (r a : SL(2,ℤ)) : ℂ := by
  classical
  exact if gamma0EisensteinCuspsEquivalent N r a then 1 else 0

theorem gamma0CuspEisenstein_leading_constant (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (y : ℝ) (hy : 0 < y) :
    (gamma0CuspTrueWidth N a:ℂ)^(-s)*(1/2:ℂ)*
      (∑' v : CuspEisensteinZeroRows N r a, cuspEisensteinRowIntegral N r a s y hy v.val)=
      gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s := by
  classical
  rw [cuspEisensteinZeroIntegral_sum]
  by_cases h : gamma0EisensteinCuspsEquivalent N r a
  · simp only [h,ite_true]
    rw [gamma0EisensteinCuspsEquivalent_width N r a h]
    have hp : (gamma0CuspTrueWidth N a:ℂ)^(-s)*(gamma0CuspTrueWidth N a:ℂ)^s=1 := by
      rw [← Complex.cpow_add _ _ (by exact_mod_cast (gamma0CuspTrueWidth_pos N a).ne')]
      simp
    simp only [gamma0CuspEisensteinIndicator,h,ite_true,one_mul]
    calc
      _=((gamma0CuspTrueWidth N a:ℂ)^(-s)*(gamma0CuspTrueWidth N a:ℂ)^s)*(y:ℂ)^s := by ring
      _=_ := by rw [hp,one_mul]
  · simp [h,gamma0CuspEisensteinIndicator]

end ArtinMatthews
