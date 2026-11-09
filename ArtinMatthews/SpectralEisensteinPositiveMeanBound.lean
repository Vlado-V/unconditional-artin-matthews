module

public import ArtinMatthews.SpectralEisensteinHorocycleComparison
public import ArtinMatthews.SpectralCuspEisensteinPositiveIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Actual positive-row remainder bounds obtained from the proved horocycle
mean, without a spectral estimate or a bound on the number of eigenvalues. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinPositiveRow_horizontal_compare (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 0 ≤ s.re) (v : CuspEisensteinPositiveRows N r a)
    (x t y : ℝ) (hy : 1 ≤ y) (hx : |x| ≤ 1) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖cuspEisensteinRowTerm N r a s v.val
      (cuspEisensteinTargetPoint N r y (lt_of_lt_of_le zero_lt_one hy) x)‖ ≤
      9^s.re*‖cuspEisensteinRowTerm N r a s v.val
        (cuspEisensteinTargetPoint N r y (lt_of_lt_of_le zero_lt_one hy) t)‖ := by
  let e := cuspEisensteinPositiveCoordinateEquiv N r a
  obtain ⟨q,hq⟩ := e.surjective v
  rcases q with ⟨c,d⟩
  have hv : cuspEisensteinPositiveCoordinateRow N r a ⟨c,d⟩=v := hq
  rw [← hv,cuspEisensteinCoordinateTerm_eq,cuspEisensteinCoordinateTerm_eq,norm_mul,norm_mul]
  have hrow := eisensteinRealRowTerm_horizontal_norm_compare s hs
    ((c.val:ℝ)*(gamma0CuspTrueWidth N r:ℝ)) d.val x t y
    (mul_pos (by exact_mod_cast c.property) (by exact_mod_cast gamma0CuspTrueWidth_pos N r)) hy hx ht
  calc
    _ ≤ ‖(gamma0CuspTrueWidth N r:ℂ)^s‖*
        (9^s.re*‖eisensteinRealRowTerm s ((c.val:ℝ)*(gamma0CuspTrueWidth N r:ℝ)) d.val t y‖) :=
      mul_le_mul_of_nonneg_left hrow (norm_nonneg _)
    _=_ := by ring

theorem cuspEisensteinPositiveRow_mean_bound (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (v : CuspEisensteinPositiveRows N r a)
    (x y : ℝ) (hy : 1 ≤ y) (hx : |x| ≤ 1) :
    ‖cuspEisensteinRowTerm N r a s v.val
      (cuspEisensteinTargetPoint N r y (lt_of_lt_of_le zero_lt_one hy) x)‖ ≤
      9^s.re*∫ t in Ioc (0:ℝ) 1, ‖cuspEisensteinRowTerm N r a s v.val
        (cuspEisensteinTargetPoint N r y (lt_of_lt_of_le zero_lt_one hy) t)‖ := by
  have hi := (cuspEisensteinRowTerm_horizontal_integrable N r a s hs y
    (lt_of_lt_of_le zero_lt_one hy) v.val).norm
  have hconst : IntegrableOn (fun _ : ℝ => ‖cuspEisensteinRowTerm N r a s v.val
      (cuspEisensteinTargetPoint N r y (lt_of_lt_of_le zero_lt_one hy) x)‖) (Ioc (0:ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h := integral_mono_ae hconst (hi.const_mul (9^s.re)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact cuspEisensteinPositiveRow_horizontal_compare N r a s (by linarith) v x t y hy hx
      (Ioc_subset_Icc_self ht))
  simpa [integral_const_mul] using h

theorem cuspEisensteinRowTerm_real_norm (N : ℕ) (r a : SL(2,ℤ)) (s : ℂ)
    (v : Gamma0CuspEisensteinRows N r a) (z : UpperHalfPlane) :
    cuspEisensteinRowTerm N r a (s.re:ℂ) v z=(‖cuspEisensteinRowTerm N r a s v z‖:ℂ) := by
  rw [cuspEisensteinRowTerm,← Complex.ofReal_cpow (cuspEisensteinRowHeight_pos N r a v z).le s.re]
  rw [cuspEisensteinRowTerm,Complex.norm_cpow_eq_rpow_re_of_pos (cuspEisensteinRowHeight_pos N r a v z)]

theorem cuspEisensteinRowIntegral_norm_eq_re (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (y : ℝ) (hy : 0 < y) (v : Gamma0CuspEisensteinRows N r a) :
    (∫ t in Ioc (0:ℝ) 1, ‖cuspEisensteinRowTerm N r a s v (cuspEisensteinTargetPoint N r y hy t)‖)=
      (cuspEisensteinRowIntegral N r a (s.re:ℂ) y hy v).re := by
  unfold cuspEisensteinRowIntegral
  simp_rw [cuspEisensteinRowTerm_real_norm]
  rw [integral_complex_ofReal,Complex.ofReal_re]

end ArtinMatthews
