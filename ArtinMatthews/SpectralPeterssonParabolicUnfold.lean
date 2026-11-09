module

public import ArtinMatthews.SpectralPeterssonCuspRows
public import ArtinMatthews.SpectralCuspEisensteinInfinity


set_option backward.privateInPublic true
@[expose] public section

/-! The actual congruence group is the signed bottom rows times the
primitive integer parabolic translations. The horizontal strip picks
exactly one translation per signed row. -/

noncomputable section
open Matrix Set UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0PeterssonParabolicExpand (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N 1 a × ℤ) : CongruenceSubgroup.Gamma0 N :=
  let M := gamma0PeterssonRowMatrix N 1 a p.1
  let T := integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*p.2)
  ⟨a⁻¹*T*M.val,by
    have hT : a⁻¹*T*a ∈ CongruenceSubgroup.Gamma0 N :=
      (gamma0CuspTrueWidth_translation_iff N a _).mpr (dvd_mul_right _ _)
    have hM : a⁻¹*M.val ∈ CongruenceSubgroup.Gamma0 N := by
      have h := M.property
      change a⁻¹*M.val*1 ∈ CongruenceSubgroup.Gamma0 N at h
      simpa only [mul_one] using h
    rw [show a⁻¹*T*M.val = (a⁻¹*T*a)*(a⁻¹*M.val) by group]
    exact (CongruenceSubgroup.Gamma0 N).mul_mem hT hM⟩

private theorem gamma0Petersson_bottomRow_left (M : SL(2, ℤ)) (l : ℤ) :
    (fun i => (integerTranslation l*M) 1 i) = fun i => M 1 i := by
  obtain ⟨_,hc,hd⟩ := integerTranslation_entries l 0 M
  have h0 : integerTranslation 0 = 1 := by simp only [integerTranslation_eq_T_zpow,zpow_zero]
  rw [h0,mul_one] at hc hd
  funext i
  fin_cases i
  · exact hc
  · change (integerTranslation l*M) 1 1 = M 1 1
    simpa only [mul_zero,add_zero] using hd

theorem gamma0PeterssonParabolicExpand_bijective (N : ℕ) [NeZero N] (a : SL(2, ℤ)) :
    Function.Bijective (gamma0PeterssonParabolicExpand N a) := by
  constructor
  · rintro ⟨p,l⟩ ⟨q,k⟩ h
    let Mp := (gamma0PeterssonRowMatrix N 1 a p).val
    let Mq := (gamma0PeterssonRowMatrix N 1 a q).val
    let Tl := integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)
    let Tk := integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*k)
    have hm : Tl*Mp = Tk*Mq := by
      calc
        _ = a*(gamma0PeterssonParabolicExpand N a (p,l)).val := by
          change Tl*Mp = a*(a⁻¹*Tl*Mp)
          group
        _ = a*(gamma0PeterssonParabolicExpand N a (q,k)).val :=
          congrArg (fun γ : CongruenceSubgroup.Gamma0 N => a*γ.val) h
        _ = _ := by
          change a*(a⁻¹*Tk*Mq) = Tk*Mq
          group
    have hrow : p.val = q.val := by
      calc
        _ = fun i => Mp 1 i := (gamma0PeterssonRowMatrix_row N 1 a p).symm
        _ = fun i => (Tl*Mp) 1 i := (gamma0Petersson_bottomRow_left Mp _).symm
        _ = fun i => (Tk*Mq) 1 i := congrArg (fun M : SL(2, ℤ) => fun i => M 1 i) hm
        _ = fun i => Mq 1 i := gamma0Petersson_bottomRow_left Mq _
        _ = _ := gamma0PeterssonRowMatrix_row N 1 a q
    have hp : p = q := Subtype.ext hrow
    have ht : Tl = Tk := mul_right_cancel (hm.trans (congrArg (fun z =>
      Tk*(gamma0PeterssonRowMatrix N 1 a z).val) hp.symm))
    have hk := congrArg (fun M : SL(2, ℤ) => M 0 1) ht
    change (gamma0CuspTrueWidth N a : ℤ)*l = (gamma0CuspTrueWidth N a : ℤ)*k at hk
    have hw : (gamma0CuspTrueWidth N a : ℤ) ≠ 0 := by exact_mod_cast (gamma0CuspTrueWidth_pos N a).ne'
    exact Prod.ext hp (mul_left_cancel₀ hw hk)
  · intro γ
    let M := gamma0CuspMatrixEquiv N 1 a γ
    let p := gamma0PeterssonRowOfMatrix N 1 a M
    let R := gamma0PeterssonRowMatrix N 1 a p
    have hR := gamma0PeterssonRowMatrix_row N 1 a p
    obtain ⟨l,hl⟩ := gamma0Petersson_left_translate_of_row_eq N 1 a R M
      (congrFun hR.symm 0) (congrFun hR.symm 1)
    refine ⟨(p,l),Subtype.ext ?_⟩
    change a⁻¹*integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)*R.val = γ.val
    have h := congrArg (fun A : SL(2, ℤ) => a⁻¹*A) hl
    change a⁻¹*(a*γ.val*1⁻¹) =
      a⁻¹*(integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)*R.val) at h
    simpa only [inv_one,mul_one,mul_assoc,inv_mul_cancel_left] using h.symm

def gamma0PeterssonParabolicEquiv (N : ℕ) [NeZero N] (a : SL(2, ℤ)) :
    (Gamma0PeterssonSignedRow N 1 a × ℤ) ≃ CongruenceSubgroup.Gamma0 N :=
  Equiv.ofBijective _ (gamma0PeterssonParabolicExpand_bijective N a)

theorem gamma0PeterssonParabolicExpand_normalized (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N 1 a) (l : ℤ) :
    (gamma0TrueCuspScaling N a)⁻¹*atkinRealMap (gamma0PeterssonParabolicExpand N a (p,l)).val =
      realTranslation (l : ℝ)*
        gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val := by
  let M := (gamma0PeterssonRowMatrix N 1 a p).val
  let T := integerTranslation ((gamma0CuspTrueWidth N a : ℤ)*l)
  let γ := gamma0PeterssonParabolicExpand N a (p,l)
  have hM : a*γ.val*1⁻¹ = T*M := by
    change a*(a⁻¹*T*M)*1⁻¹ = T*M
    group
  have h := gamma0TrueWidthMatrix_correspondence N 1 a γ
  rw [hM,gamma0Petersson_normalized_left_translate,
    gamma0TrueCuspScaling_identity,mul_one] at h
  exact h.symm

def spectralPeterssonStripLift (x : ℝ) : ℤ := ⌊-x⌋ + 1

theorem spectralPeterssonStripLift_mem (x : ℝ) :
    x+(spectralPeterssonStripLift x : ℝ) ∈ Ioc (0 : ℝ) 1 := by
  have h₁ := Int.floor_le (-x)
  have h₂ := Int.lt_floor_add_one (-x)
  unfold spectralPeterssonStripLift
  push_cast
  exact ⟨by linarith,by linarith⟩

theorem spectralPeterssonStripLift_unique (x : ℝ) (l : ℤ)
    (hl : x+(l : ℝ) ∈ Ioc (0 : ℝ) 1) : l = spectralPeterssonStripLift x := by
  have h := spectralPeterssonStripLift_mem x
  have h₁ : (l : ℝ)-(spectralPeterssonStripLift x : ℝ) < 1 := by linarith [hl.2,h.1]
  have h₂ : (spectralPeterssonStripLift x : ℝ)-(l : ℝ) < 1 := by linarith [h.2,hl.1]
  have h₁' : l-spectralPeterssonStripLift x < (1 : ℤ) := by exact_mod_cast h₁
  have h₂' : spectralPeterssonStripLift x-l < (1 : ℤ) := by exact_mod_cast h₂
  omega

end ArtinMatthews
