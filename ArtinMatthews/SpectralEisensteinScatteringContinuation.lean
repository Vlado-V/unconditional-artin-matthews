module

public import ArtinMatthews.SpectralEisensteinInitialConstant


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine holomorphic all-cusp scattering continuation off the ambient
spectral cut, proved to equal the original convergent Eisenstein coefficient.
Critical-line boundary values and global automorphic resolution are separate. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspEisensteinContinuedCoefficient_initial (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re) :
    gamma0CuspEisensteinContinuedCoefficient N r a s=
      (gamma0CuspTrueWidth N r:ℂ)^(s-1)*gamma0CuspScattering N r a s := by
  let Y : ℝ := 2*(gamma0CuspTrueWidth N r:ℝ)
  have hY : 0<Y := mul_pos (by norm_num) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))
  have hw : 0<(N:ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hg := gamma0CuspEisensteinRemainder_global_constant_initial N r a s hs
  have he : gamma0GlobalCuspConstantTerm N r (gamma0CuspEisensteinRemainderMass N a s hs)
      =ᵐ[volume.restrict (Ioi Y)]
        gamma0CuspConstantTerm N r Y hY (gamma0CuspEisensteinRemainderMass N a s hs) :=
    (spectralCuspVerticalL2_ae_iff hw hY).mp
      (gamma0GlobalCuspConstantTerm_ae N r (gamma0CuspEisensteinRemainderMass N a s hs) Y hY)
  have hU := (spectralCuspVerticalL2_ae_iff hw hY).mpr (he.symm.trans hg)
  change cuspEulerCoefficientExtract hw hY s
    (gamma0CuspConstantTerm N r Y hY (gamma0CuspEisensteinContinuedRemainder N a s))=_
  rw [gamma0CuspEisensteinContinuedRemainder_initial N a s hs]
  exact cuspEulerCoefficientExtract_power hw hY s _ (by linarith) _ hU

theorem gamma0CuspScatteringContinued_initial (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re) :
    gamma0CuspScatteringContinued N r a s=gamma0CuspScattering N r a s := by
  rw [gamma0CuspScatteringContinued,gamma0CuspEisensteinContinuedCoefficient_initial N r a s hs,
    ← mul_assoc,← Complex.cpow_add _ _ (by exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne'),
    show 1-s+(s-1)=0 by ring,Complex.cpow_zero,one_mul]

theorem gamma0CuspScatteringContinued_analyticOn (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) :
    AnalyticOnNhd ℂ (gamma0CuspScatteringContinued N r a) gamma0EisensteinContinuationDomain :=
  fun s hs => gamma0CuspScatteringContinued_analyticAt N r a s hs

theorem gamma0CuspEisensteinContinuedCoefficient_height_independent
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (hs : s ∈ gamma0EisensteinContinuationDomain) (Y : ℝ) (hY : 0<Y)
    (hhigh : 2*(gamma0CuspTrueWidth N r:ℝ)≤Y) :
    cuspEulerCoefficientExtract (Nat.cast_pos.mpr (NeZero.pos N)) hY s
      (gamma0CuspConstantTerm N r Y hY (gamma0CuspEisensteinContinuedRemainder N a s))=
      gamma0CuspEisensteinContinuedCoefficient N r a s := by
  have hmode := ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi hhigh)
    (gamma0CuspEisensteinContinuedCoefficient_mode N r a s hs)
  have he : gamma0GlobalCuspConstantTerm N r (gamma0CuspEisensteinContinuedRemainder N a s)
      =ᵐ[volume.restrict (Ioi Y)]
        gamma0CuspConstantTerm N r Y hY (gamma0CuspEisensteinContinuedRemainder N a s) :=
    (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
      (gamma0GlobalCuspConstantTerm_ae N r (gamma0CuspEisensteinContinuedRemainder N a s) Y hY)
  exact cuspEulerCoefficientExtract_power (Nat.cast_pos.mpr (NeZero.pos N)) hY s _ hs.1 _
    ((spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mpr (he.symm.trans hmode))

theorem gamma0CuspEisensteinContinuedRemainder_normalized_constant_mode
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ)
    (hs : s ∈ gamma0EisensteinContinuationDomain) :
    gamma0GlobalCuspConstantTerm N r (gamma0CuspEisensteinContinuedRemainder N a s)
      =ᵐ[volume.restrict (Ioi (2*(gamma0CuspTrueWidth N r:ℝ)))]
        fun y => gamma0CuspScatteringContinued N r a s*
          ((y/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^(1-s) := by
  filter_upwards [gamma0CuspEisensteinContinuedCoefficient_mode N r a s hs,
    ae_restrict_mem measurableSet_Ioi] with y hy hyY
  have hw : (0:ℝ)<gamma0CuspTrueWidth N r := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hy0 : 0<y := (mul_pos (by norm_num : (0:ℝ)<2) hw).trans hyY
  rw [hy,gamma0CuspScatteringContinued,Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hy0.le hw.le]
  have hn : (gamma0CuspTrueWidth N r:ℂ)^(1-s)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne'))
  simp only [Complex.ofReal_natCast]
  field_simp

theorem gamma0CuspEisenstein_initial_constant_matrix_continued
    (N : ℕ) [NeZero N] (r a : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re) (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..1, gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x))=
      gamma0CuspEisensteinIndicator N r a*(y:ℂ)^s+
        (y:ℂ)^(1-s)*gamma0CuspScatteringContinued N r a s := by
  rw [gamma0CuspScatteringContinued_initial N r a s hs]
  exact gamma0CuspEisenstein_all_cusp_constant_term N r a s hs y hy

end ArtinMatthews
