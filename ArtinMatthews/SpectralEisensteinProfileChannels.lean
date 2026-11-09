module

public import ArtinMatthews.SpectralCompactMellinScaling
public import ArtinMatthews.SpectralEisensteinKernelLocalization


set_option backward.privateInPublic true
@[expose] public section

/-! Concrete dilates of the fixed smooth bump give actual compact
Eisenstein coefficient rows. Every source and target cusp stays explicit. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

def gamma0ProbeDilate (c y : ℝ) : ℂ := (gamma0ResidualProbeBump (y/c):ℂ)

theorem gamma0ProbeDilate_smooth (c : ℝ) : ContDiff ℝ ∞ (gamma0ProbeDilate c) :=
  (Complex.ofRealCLM.contDiff.comp gamma0ResidualProbeBump.contDiff).comp (contDiff_id.div_const c)

theorem gamma0ProbeDilate_compact {c : ℝ} (hc : 0<c) : HasCompactSupport (gamma0ProbeDilate c) :=
  cuspHeightProfile_scaled_compact c hc (fun y => (gamma0ResidualProbeBump y:ℂ))
    (gamma0ResidualProbeBump.hasCompactSupport.comp_left Complex.ofReal_zero)

theorem gamma0ProbeDilate_positive {c : ℝ} (hc : 0<c) : tsupport (gamma0ProbeDilate c)⊆Ioi (0:ℝ) := by
  apply cuspHeightProfile_scaled_support c hc (fun y => (gamma0ResidualProbeBump y:ℂ))
  have hs : Function.support (fun y : ℝ => (gamma0ResidualProbeBump y:ℂ))⊆
      Function.support gamma0ResidualProbeBump := by
    intro y hy hz
    exact hy (by
      change (gamma0ResidualProbeBump y:ℂ)=0
      rw [hz,Complex.ofReal_zero])
  exact (closure_mono hs).trans (gamma0ResidualProbeBump_tsupport.trans (Ioi_subset_Ioi zero_le_one))

theorem gamma0ProbeDilate_high (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N)
    {c : ℝ} (hc : 0<c) (hH : gamma0EisensteinMatchingHeight N≤c) :
    ∀ y≤gamma0EisensteinMatchingHeight N,
      gamma0ProbeDilate c (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ))=0 := by
  let w : ℝ := gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i)
  have hw : 0<w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N _)
  have hw1 : 1≤w := by
    dsimp only [w]
    exact_mod_cast (Nat.succ_le_iff.mpr (gamma0CuspTrueWidth_pos N (gamma0EisensteinCuspClassRepresentative N i)))
  intro y hy
  have hl : (y/w)/c≤1 := by
    rw [div_le_iff₀ hc,one_mul,div_le_iff₀ hw]
    exact hy.trans (hH.trans (le_mul_of_one_le_right hc.le hw1))
  have hz : gamma0ResidualProbeBump ((y/w)/c)=0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => (not_lt_of_ge hl) (gamma0ResidualProbeBump_tsupport hm))
  change (gamma0ResidualProbeBump ((y/w)/c):ℂ)=0
  rw [hz,Complex.ofReal_zero]

def gamma0ProbeHighSeed (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N)
    (c : ℝ) (hc : 0<c) : h2SmoothCompactSeeds :=
  gamma0EisensteinHighProfileSeed N i (gamma0ProbeDilate c) (gamma0ProbeDilate_smooth c)
    (gamma0ProbeDilate_compact hc) (gamma0ProbeDilate_positive hc)

theorem gamma0ProbeHighSeed_actual_test (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N)
    (a : SL(2,ℤ)) {c : ℝ} (hc : 0<c) (hH : gamma0EisensteinMatchingHeight N≤c) (s : ℂ) :
    gamma0CuspEisensteinMeromorphicTest N a (gamma0ProbeHighSeed N i c hc) s=
      gamma0CuspEisensteinIndicator N (gamma0EisensteinCuspClassRepresentative N i) a*
        ((c:ℂ)^(s-1)*gamma0ProbeMellin s)+
      gamma0EisensteinMatchedCoefficient N a s i*((c:ℂ)^(-s)*gamma0ProbeMellin (1-s)) := by
  rw [gamma0ProbeHighSeed,gamma0EisensteinHighProfile_actual_mellin N i a _ _ _ _
    (gamma0ProbeDilate_high N i hc hH)]
  change _=gamma0CuspEisensteinIndicator N (gamma0EisensteinCuspClassRepresentative N i) a*
      ((c:ℂ)^(s-1)*spectralCompactCuspMellin (fun y => (gamma0ResidualProbeBump y:ℂ)) s)+
    gamma0EisensteinMatchedCoefficient N a s i*((c:ℂ)^(-s)*
      spectralCompactCuspMellin (fun y => (gamma0ResidualProbeBump y:ℂ)) (1-s))
  unfold gamma0ProbeDilate
  rw [spectralCompactCuspMellin_dilate hc (fun y => (gamma0ResidualProbeBump y:ℂ)) s,
    spectralCompactCuspMellin_dilate hc (fun y => (gamma0ResidualProbeBump y:ℂ)) (1-s),
    show (1-s)-1=-s by ring]

theorem gamma0EisensteinSynthesis_kernel_seed_amplitudes (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) (hv : (gamma0EisensteinAnalysis N).adjoint v=0)
    (ψ : h2SmoothCompactSeeds) :
    ∀ᵐ t ∂gamma0EisensteinSpectralMeasure,
      (∑ j : Gamma0EisensteinCuspClasses N,
        gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N j) ψ
          (eisensteinCriticalPoint t)*v j t)=0 := by
  have h := gamma0EisensteinSynthesis_kernel_fiber N v hv (gamma0SmoothSeedMass N ψ)
  rw [gamma0EisensteinAnalysis_seed] at h
  have ha : ∀ᵐ t ∂gamma0EisensteinSpectralMeasure,∀ j : Gamma0EisensteinCuspClasses N,
      gamma0EisensteinCoefficientLp N j ψ t=(starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ j t) :=
    ae_all_iff.mpr (fun j => gamma0EisensteinCoefficientLp_ae N j ψ)
  filter_upwards [h,ha] with t ht hat
  have he : gamma0EisensteinChannelPair N (gamma0EisensteinSeedAnalysis N ψ) v t=
      ∑ j : Gamma0EisensteinCuspClasses N,
        gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N j) ψ
          (eisensteinCriticalPoint t)*v j t := by
    unfold gamma0EisensteinChannelPair
    apply Finset.sum_congr rfl
    intro j _
    rw [gamma0EisensteinSeedAnalysis_apply,hat j,RCLike.inner_apply,
      show (starRingEnd ℂ) ((starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ j t))=
        gamma0StoneEisensteinAmplitude N ψ j t from star_star _]
    exact mul_comm _ _
  rw [← he]
  exact ht

theorem gamma0EisensteinProfile_row_sum (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N)
    (α β : ℂ) (p q : Gamma0EisensteinCuspClasses N → ℂ) :
    (∑ j,(gamma0CuspEisensteinIndicator N (gamma0EisensteinCuspClassRepresentative N i)
      (gamma0EisensteinCuspClassRepresentative N j)*α+p j*β)*q j)=
      α*q i+β*(∑ j,p j*q j) := by
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single i]
    · simp [gamma0CuspEisensteinIndicator_eq_cuspClass]
    · intro j _ hj
      rw [gamma0CuspEisensteinIndicator_eq_cuspClass,gamma0EisensteinCuspClassRepresentative_class,
        gamma0EisensteinCuspClassRepresentative_class,ite_eq_right hj.symm,zero_mul,zero_mul]
    · simp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem gamma0EisensteinSynthesis_kernel_profile_equation (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) (hv : (gamma0EisensteinAnalysis N).adjoint v=0)
    (i : Gamma0EisensteinCuspClasses N) {c : ℝ} (hc : 0<c) (hH : gamma0EisensteinMatchingHeight N≤c) :
    ∀ᵐ t ∂gamma0EisensteinSpectralMeasure,
      (c:ℂ)^(eisensteinCriticalPoint t-1)*gamma0ProbeMellin (eisensteinCriticalPoint t)*v i t+
      ((c:ℂ)^(-eisensteinCriticalPoint t)*gamma0ProbeMellin (1-eisensteinCriticalPoint t))*
        (∑ j : Gamma0EisensteinCuspClasses N,
          gamma0EisensteinMatchedCoefficient N (gamma0EisensteinCuspClassRepresentative N j)
            (eisensteinCriticalPoint t) i*v j t)=0 := by
  have h := gamma0EisensteinSynthesis_kernel_seed_amplitudes N v hv (gamma0ProbeHighSeed N i c hc)
  filter_upwards [h] with t ht
  simp_rw [gamma0ProbeHighSeed_actual_test N i _ hc hH] at ht
  rw [gamma0EisensteinProfile_row_sum] at ht
  simpa only [mul_assoc] using ht

end ArtinMatthews
