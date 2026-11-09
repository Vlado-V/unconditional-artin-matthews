module

public import ArtinMatthews.TameQuadraticGauss


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine quadratic cancellation, including an arbitrary linear coefficient. -/
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
namespace ArtinMatthews.PrimePowerWeil

variable {F : Type*} [Field F] [Fintype F]

theorem quadraticGauss_norm (hF : ringChar F≠2) (ψ : AddChar F ℂ) (hψ : ψ≠1)
    {a : F} (ha : a≠0) :
    ‖∑ x : F, ψ (a*x^2)‖=Real.sqrt (Fintype.card F) := by
  have hχ : ‖QuadraticGauss.residueCharacter F a‖=1 := by
    have h := congrArg norm (QuadraticGauss.residueCharacter_sq ha)
    simp only [norm_pow,norm_one] at h
    nlinarith [norm_nonneg (QuadraticGauss.residueCharacter F a)]
  have hq : 0<(Fintype.card F:ℝ) := by exact_mod_cast Fintype.card_pos (α := F)
  have hG := QuadraticGauss.residueIndex_norm hF ψ hψ
  unfold QuadraticGauss.residueIndex ProbeGauss.normalizedGauss at hG
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hG
  have hg := (div_eq_one_iff_eq (Real.sqrt_ne_zero'.mpr hq)).mp hG
  rw [QuadraticGauss.square_sum_scaled hF ψ hψ ha,norm_mul,hχ,hg,one_mul]

theorem quadraticAffineGauss_norm (hF : ringChar F≠2) (h2 : (2:F)≠0)
    (ψ : AddChar F ℂ) (hψ : ψ≠1) {a : F} (ha : a≠0) (b : F) :
    ‖∑ x : F, ψ (a*x^2+b*x)‖=Real.sqrt (Fintype.card F) := by
  classical
  let c := b/(2*a)
  have hc : 2*a*c=b := by dsimp [c]; field_simp
  have hpoly (x : F) : a*(x+c)^2=(a*x^2+b*x)+a*c^2 := by
    linear_combination x*hc
  have he : (∑ x : F, ψ (a*x^2))=(∑ x : F, ψ (a*x^2+b*x))*ψ (a*c^2) := by
    rw [← Equiv.sum_comp (Equiv.addRight c) (fun x : F => ψ (a*x^2))]
    change (∑ x : F, ψ (a*(x+c)^2))=_
    simp_rw [hpoly,AddChar.map_add_eq_mul]
    rw [Finset.sum_mul]
  have hn := congrArg norm he
  rw [norm_mul,AddChar.norm_apply,mul_one] at hn
  exact hn.symm.trans (quadraticGauss_norm hF ψ hψ ha)

end ArtinMatthews.PrimePowerWeil
