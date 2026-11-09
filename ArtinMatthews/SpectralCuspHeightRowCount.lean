module

public import ArtinMatthews.SpectralPlanarRowPacking
public import ArtinMatthews.SpectralCuspRowDeterminants


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform overlap of actual normalized cusp heights. Both central
signs are counted as distinct rows. -/

noncomputable section
open Set Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem cuspEisensteinHeightRows_finite (N : ℕ) (a : SL(2, ℤ)) (z : UpperHalfPlane)
    {A : ℝ} (hA : 0 < A) :
    {v : Gamma0CuspEisensteinRows N 1 a | A ≤ cuspEisensteinRowHeight N 1 a v z}.Finite := by
  have hS := cuspEisensteinRowTerm_summable_norm N 1 a 2 (by norm_num) z
  have hE := hS.tendsto_cofinite_zero.eventually_lt_const (sq_pos_of_pos hA)
  apply (Filter.eventually_cofinite.mp hE).subset
  intro u hu
  change ¬‖cuspEisensteinRowTerm N 1 a (2 : ℂ) u z‖ < A^2
  have h := cuspEisensteinRowHeight_pos N 1 a u z
  rw [cuspEisensteinRowTerm,show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
    Complex.cpow_natCast,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos h]
  exact not_lt_of_ge (pow_le_pow_left₀ hA.le hu 2)

def cuspEisensteinHeightRows (N : ℕ) (a : SL(2, ℤ)) (z : UpperHalfPlane)
    (A : ℝ) (hA : 0 < A) : Finset (Gamma0CuspEisensteinRows N 1 a) :=
  (cuspEisensteinHeightRows_finite N a z hA).toFinset

theorem cuspEisensteinHeightRows_mem (N : ℕ) (a : SL(2, ℤ)) (z : UpperHalfPlane)
    {A : ℝ} (hA : 0 < A) (v : Gamma0CuspEisensteinRows N 1 a) :
    v ∈ cuspEisensteinHeightRows N a z A hA ↔ A ≤ cuspEisensteinRowHeight N 1 a v z :=
  (cuspEisensteinHeightRows_finite N a z hA).mem_toFinset

theorem cuspEisensteinHeightRows_card_le (N D : ℕ) (a : SL(2, ℤ))
    (hD : 0 < D) (hmod : ∀ M ∈ gamma0CuspCorrespondence N a a, (D : ℤ) ∣ M 1 0)
    (z : UpperHalfPlane) {A : ℝ} (hA : 0 < A) :
    ((cuspEisensteinHeightRows N a z A hA).card : ℝ) ≤ 4*(1+2/((D : ℝ)*A)) := by
  let S := cuspEisensteinHeightRows N a z A hA
  let v (u : Gamma0CuspEisensteinRows N 1 a) : ℝ×ℝ :=
    ((u.val 0 : ℝ)*z.im,(u.val 0 : ℝ)*z.re+u.val 1)
  let R := Real.sqrt (z.im/A)
  have hy : 0 < z.im := z.im_pos
  have hR : 0 < R := Real.sqrt_pos.2 (div_pos hy hA)
  have hRsq : R^2 = z.im/A := Real.sq_sqrt (div_nonneg hy.le hA.le)
  have hD' : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have hv (u : Gamma0CuspEisensteinRows N 1 a) (hu : u ∈ S) :
      v u ≠ (0,0) ∧ |(v u).1| ≤ R ∧ |(v u).2| ≤ R := by
    have hz : v u ≠ (0,0) := by
      intro he
      have hc := congrArg Prod.fst he
      change (u.val 0 : ℝ)*z.im = 0 at hc
      have hcz := (mul_eq_zero.mp hc).resolve_right hy.ne'
      have hc₀ : u.val 0 = 0 := by exact_mod_cast hcz
      have hd := congrArg Prod.snd he
      change (u.val 0 : ℝ)*z.re+u.val 1 = 0 at hd
      rw [hcz,zero_mul,zero_add] at hd
      have hd₀ : u.val 1 = 0 := by exact_mod_cast hd
      apply gamma0CuspEisensteinRows_ne_zero N 1 a u
      funext j
      fin_cases j
      · exact hc₀
      · exact hd₀
    let Q := ‖(u.val 0 : ℂ)*(z : ℂ)+u.val 1‖^2
    have hQ : 0 < Q := by
      by_contra! hn
      have hq : Q = 0 := le_antisymm hn (sq_nonneg _)
      have hp := cuspEisensteinRowHeight_pos N 1 a u z
      rw [cuspEisensteinRowHeight_row,show ‖(u.val 0 : ℂ)*(z : ℂ)+u.val 1‖^2 = Q from rfl,
        hq,div_zero] at hp
      exact (lt_irrefl _) hp
    have hnorm : Q = ((v u).1)^2+((v u).2)^2 := by
      dsimp only [Q,v]
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.intCast_re,
        Complex.intCast_im,zero_mul,sub_zero,add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
      ring
    have hH := (cuspEisensteinHeightRows_mem N a z hA u).mp hu
    rw [cuspEisensteinRowHeight_row] at hH
    change A ≤ z.im/Q at hH
    have hQle : Q ≤ z.im/A := (le_div_iff₀ hA).mpr (by
      rw [mul_comm]
      exact (le_div_iff₀ hQ).mp hH)
    rw [hnorm] at hQle
    exact ⟨hz,(Real.le_sqrt (abs_nonneg _) (div_nonneg hy.le hA.le)).mpr (by
      rw [sq_abs]; linarith [sq_nonneg (v u).2]),
      (Real.le_sqrt (abs_nonneg _) (div_nonneg hy.le hA.le)).mpr (by
        rw [sq_abs]; linarith [sq_nonneg (v u).1])⟩
  have hd (u : Gamma0CuspEisensteinRows N 1 a) (_ : u ∈ S)
      (w : Gamma0CuspEisensteinRows N 1 a) (_ : w ∈ S) (hne : u ≠ w) :
      ((v u).1 = -(v w).1 ∧ (v u).2 = -(v w).2) ∨
        (D : ℝ)*z.im ≤ |(v u).1*(v w).2-(v u).2*(v w).1| := by
    rcases cuspEisensteinRows_det_antipodal_or_lower_bound N D a hmod u w hne with h | h
    · left
      have h₀ := congrFun h 0
      have h₁ := congrFun h 1
      dsimp only [v]
      simp only [h₀,h₁,Pi.neg_apply,Int.cast_neg]
      constructor <;> ring
    · right
      have he : (v u).1*(v w).2-(v u).2*(v w).1 =
          z.im*(((u.val 0*w.val 1-u.val 1*w.val 0 : ℤ) : ℝ)) := by
        dsimp only [v]
        push_cast
        ring
      have habs : (D : ℝ) ≤ |((u.val 0*w.val 1-u.val 1*w.val 0 : ℤ) : ℝ)| := by
        exact_mod_cast h
      rw [he,abs_mul,abs_of_pos hy,mul_comm (D : ℝ) z.im]
      exact mul_le_mul_of_nonneg_left habs hy.le
  have h := spectral_card_le_planar_rows S v hR (mul_pos hD' hy) hv hd
  refine h.trans_eq ?_
  rw [hRsq]
  field_simp [hy.ne',hA.ne',hD'.ne']

theorem gamma0Infinity_heightRows_card_le (N : ℕ) [NeZero N] (z : UpperHalfPlane)
    {A : ℝ} (hA : 0 < A) :
    ((cuspEisensteinHeightRows N 1 z A hA).card : ℝ) ≤ 4*(1+2/((N : ℝ)*A)) :=
  cuspEisensteinHeightRows_card_le N N 1 (NeZero.pos N) (gamma0Infinity_sameCusp_lower_dvd N) z hA

theorem gamma0MixedCusp_heightRows_card_le (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (z : UpperHalfPlane) {A : ℝ} (hA : 0 < A) :
    let w := (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)
    let hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos (r*s) (gamma0CuspOneOver s))
    ((cuspEisensteinHeightRows (r*s) (gamma0CuspOneOver s) z (w*A) (mul_pos hw hA)).card : ℝ) ≤
      4*(1+2/((r*s : ℕ)*A)) := by
  dsimp only
  have hw : 0 < (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ) :=
    Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos (r*s) (gamma0CuspOneOver s))
  have h := cuspEisensteinHeightRows_card_le (r*s) s (gamma0CuspOneOver s) (NeZero.pos s)
    (gamma0MixedCusp_sameCusp_lower_dvd r s) z
    (mul_pos hw hA)
  refine h.trans_eq ?_
  rw [gamma0MixedCusp_trueWidth r s hcop]
  push_cast
  ring

end ArtinMatthews
