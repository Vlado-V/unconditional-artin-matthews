module

public import ArtinMatthews.SpectralGamma0EisensteinSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The literal half-row normalization and a genuine nonzero Eisenstein family. -/
noncomputable section
open Set Filter
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0EisensteinIdentityRow (N : ℕ) : Gamma0EisensteinRows N :=
  ⟨gamma0EisensteinRow N 1,⟨1,rfl⟩⟩

def gamma0EisensteinNegativeIdentity (N : ℕ) : CongruenceSubgroup.Gamma0 N :=
  ⟨-1,by simp [CongruenceSubgroup.Gamma0_mem]⟩

def gamma0EisensteinNegativeRow (N : ℕ) : Gamma0EisensteinRows N :=
  ⟨gamma0EisensteinRow N (gamma0EisensteinNegativeIdentity N),⟨_,rfl⟩⟩

theorem gamma0Eisenstein_signed_rows_ne (N : ℕ) :
    gamma0EisensteinIdentityRow N ≠ gamma0EisensteinNegativeRow N := by
  intro h
  have he := congrArg (fun v : Gamma0EisensteinRows N => v.val 1) h
  norm_num [gamma0EisensteinIdentityRow,gamma0EisensteinNegativeRow,
    gamma0EisensteinNegativeIdentity,gamma0EisensteinRow] at he

theorem gamma0Eisenstein_identity_height (N : ℕ) (z : UpperHalfPlane) :
    gamma0EisensteinHeight N (gamma0EisensteinIdentityRow N) z = z.im := by
  rw [gamma0EisensteinHeight_of_row N _ 1 rfl]
  simp

theorem gamma0Eisenstein_negative_height (N : ℕ) (z : UpperHalfPlane) :
    gamma0EisensteinHeight N (gamma0EisensteinNegativeRow N) z = z.im := by
  rw [gamma0EisensteinHeight_of_row N _ (gamma0EisensteinNegativeIdentity N) rfl]
  change ((-1 : SL(2,ℤ)) • z).im = z.im
  rw [ModularGroup.SL_neg_smul,one_smul]

theorem gamma0Eisenstein_real (N : ℕ) (s : ℝ) (z : UpperHalfPlane) :
    gamma0Eisenstein N (s : ℂ) z =
      (((1/2 : ℝ) * ∑' v : Gamma0EisensteinRows N, (gamma0EisensteinHeight N v z)^s : ℝ) : ℂ) := by
  unfold gamma0Eisenstein gamma0EisensteinSummand
  simp_rw [← Complex.ofReal_cpow (gamma0EisensteinHeight_pos N _ z).le s]
  rw [← Complex.ofReal_tsum]
  push_cast
  rfl

theorem gamma0Eisenstein_real_lower_bound (N : ℕ) (s : ℝ) (hs : 1 < s)
    (z : UpperHalfPlane) : z.im^s ≤ (gamma0Eisenstein N (s : ℂ) z).re := by
  have hsum : Summable (fun v : Gamma0EisensteinRows N => (gamma0EisensteinHeight N v z)^s) := by
    simpa only [gamma0EisensteinSummand_norm,Complex.ofReal_re] using
      gamma0EisensteinSummand_summable_norm N (s : ℂ) (by simpa using hs) z
  have h := hsum.sum_le_tsum {gamma0EisensteinIdentityRow N,gamma0EisensteinNegativeRow N}
    (fun v _ => Real.rpow_nonneg (gamma0EisensteinHeight_pos N v z).le s)
  have hn : gamma0EisensteinIdentityRow N ∉ ({gamma0EisensteinNegativeRow N} : Finset (Gamma0EisensteinRows N)) := by
    simpa only [Finset.mem_singleton] using gamma0Eisenstein_signed_rows_ne N
  simp only [Finset.sum_insert hn,
    Finset.sum_singleton,gamma0Eisenstein_identity_height,gamma0Eisenstein_negative_height] at h
  rw [gamma0Eisenstein_real]
  simp only [Complex.ofReal_re]
  linarith

theorem gamma0Eisenstein_real_ne_zero (N : ℕ) (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    gamma0Eisenstein N (s : ℂ) z ≠ 0 := by
  have hp := (Real.rpow_pos_of_pos z.im_pos s).trans_le (gamma0Eisenstein_real_lower_bound N s hs z)
  intro hz
  rw [hz,Complex.zero_re] at hp
  exact lt_irrefl _ hp

def gamma0EisensteinTranslation (N : ℕ) : CongruenceSubgroup.Gamma0 N :=
  ⟨ModularGroup.T,by simp [CongruenceSubgroup.Gamma0_mem]⟩

theorem gamma0Eisenstein_translation_invariant (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) : gamma0Eisenstein N s (ModularGroup.T • z) = gamma0Eisenstein N s z :=
  gamma0Eisenstein_automorphy N s hs (gamma0EisensteinTranslation N) z

end ArtinMatthews
