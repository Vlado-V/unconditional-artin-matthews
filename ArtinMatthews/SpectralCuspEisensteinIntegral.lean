module

public import ArtinMatthews.SpectralCuspEisensteinAutomorphy
public import ArtinMatthews.SpectralGamma0EisensteinIntegralExchange


set_option backward.privateInPublic true
@[expose] public section

/-! Actual absolute Fubini on a normalized target-cusp horocycle. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

def cuspEisensteinTargetPoint (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (y : ℝ) (hy : 0 < y) (x : ℝ) : UpperHalfPlane :=
  cuspWidthDilation (gamma0CuspTrueWidth N r:ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r) • gamma0EisensteinHorizontalPoint y hy x

theorem cuspEisensteinTargetPoint_continuous (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (y : ℝ) (hy : 0 < y) : Continuous (cuspEisensteinTargetPoint N r y hy) :=
  (continuous_const_smul _).comp (gamma0EisensteinHorizontalPoint_continuous y hy)

def cuspEisensteinRowIntegral (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (y : ℝ) (hy : 0 < y) (v : Gamma0CuspEisensteinRows N r a) : ℂ :=
  ∫ x in Ioc (0:ℝ) 1, cuspEisensteinRowTerm N r a s v (cuspEisensteinTargetPoint N r y hy x)

theorem cuspEisensteinRowTerm_horizontal_integrable (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) (v : Gamma0CuspEisensteinRows N r a) :
    IntegrableOn (fun x => cuspEisensteinRowTerm N r a s v (cuspEisensteinTargetPoint N r y hy x))
      (Ioc (0:ℝ) 1) :=
  ((cuspEisensteinRowTerm_continuous N r a s hs v).comp
    (cuspEisensteinTargetPoint_continuous N r y hy)).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem cuspEisensteinRowIntegral_norm_summable (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    Summable (fun v : Gamma0CuspEisensteinRows N r a => ∫ x in Ioc (0:ℝ) 1,
      ‖cuspEisensteinRowTerm N r a s v (cuspEisensteinTargetPoint N r y hy x)‖) := by
  have hK := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).image
    (cuspEisensteinTargetPoint_continuous N r y hy)
  obtain ⟨u,hu,hb⟩ := cuspEisensteinRowTerm_compact_majorant N r a s hs hK
  apply hu.of_nonneg_of_le (fun v => integral_nonneg (fun x => norm_nonneg _))
  intro v
  have hi := (cuspEisensteinRowTerm_horizontal_integrable N r a s hs y hy v).norm
  have hc : IntegrableOn (fun _ : ℝ => u v) (Ioc (0:ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hle := integral_mono_ae hi hc (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hb v _ ⟨x,Ioc_subset_Icc_self hx,rfl⟩)
  simpa using hle

theorem cuspEisensteinRowIntegral_summable (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    Summable (cuspEisensteinRowIntegral N r a s y hy) :=
  (cuspEisensteinRowIntegral_norm_summable N r a s hs y hy).of_norm_bounded
    (f := cuspEisensteinRowIntegral N r a s y hy) (fun _ => norm_integral_le_integral_norm _)

theorem gamma0CuspEisenstein_constant_integral_rows (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0:ℝ)..1, gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)) =
      (gamma0CuspTrueWidth N a:ℂ)^(-s)*(1/2:ℂ)*
        ∑' v : Gamma0CuspEisensteinRows N r a, cuspEisensteinRowIntegral N r a s y hy v := by
  simp_rw [gamma0CuspEisenstein_target_scaling]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  unfold cuspEisensteinRowSum
  rw [integral_const_mul,integral_const_mul]
  change (gamma0CuspTrueWidth N a:ℂ)^(-s)*((1/2:ℂ)*
    ∫ x in Ioc (0:ℝ) 1, ∑' v : Gamma0CuspEisensteinRows N r a,
      cuspEisensteinRowTerm N r a s v (cuspEisensteinTargetPoint N r y hy x))=_
  rw [← integral_tsum_of_summable_integral_norm
    (cuspEisensteinRowTerm_horizontal_integrable N r a s hs y hy)
    (cuspEisensteinRowIntegral_norm_summable N r a s hs y hy),mul_assoc]
  rfl

end ArtinMatthews
