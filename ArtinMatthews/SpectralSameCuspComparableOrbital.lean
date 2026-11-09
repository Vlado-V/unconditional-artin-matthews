module

public import ArtinMatthews.SpectralWeylComparableHeight
public import ArtinMatthews.SpectralInfinityCommonPhysicalBessel


set_option backward.privateInPublic true
@[expose] public section

/-! The comparable-height estimate for a genuine same-cusp physical
profile, with the raw width factor and true modulus both visible. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem spectralFrequencyTestProfile_scaled_comparable_support (F : ℝ → ℝ) {A freq w : ℝ}
    (hfreq : 0 < freq) (hw : 0 < w) (hF : tsupport F ⊆ Icc A (2*A)) :
    Function.support (fun y => spectralFrequencyTestProfile (freq/w) F (w*y)) ⊆
      Icc (A/freq) (2*(A/freq)) := by
  intro y hy
  have hf : (freq/w)*(w*y) ∈ tsupport F :=
    spectralFrequencyTestProfile_tsupport (freq/w) F (subset_tsupport _ hy)
  have hscale : (freq/w)*(w*y) = freq*y := by field_simp [hw.ne']
  rw [hscale] at hf
  have hb := hF hf
  refine ⟨(div_le_iff₀ hfreq).mpr (by simpa only [mul_comm] using hb.1),?_⟩
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hfreq).mpr (by simpa only [mul_comm] using hb.2)

theorem spectralFrequencyTestProfile_scaled_norm_le (F : ℝ → ℝ)
    (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (p : ℝ) {w : ℝ} (hw : 0 < w) (y : ℝ) :
    ‖spectralFrequencyTestProfile p F (w*y)‖ ≤ Real.sqrt y*Real.sqrt w := by
  have hf := h01 (p*(w*y))
  rw [spectralFrequencyTestProfile,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg hf.1,Real.sqrt_mul hw.le]
  calc
    _ ≤ Real.sqrt w*Real.sqrt y*1 := mul_le_mul_of_nonneg_left hf.2 (by positivity)
    _ = _ := by ring

theorem gamma0TrueWidthBesselOrbital_sameCusp_comparable_physical (N q : ℕ) [NeZero N] [NeZero q]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) {A : ℝ} (hA : 0 < A)
    (hSF : tsupport F ⊆ Icc A (2*A)) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    let w := (gamma0CuspTrueWidth N r : ℝ)
    let ρ := spectralFrequencyTestProfile (|cuspFourierFrequency 1 n|/w) F
    ‖gamma0TrueWidthBesselOrbital N r r q n n ρ ρ‖ ≤
      8*w/gamma0TrueWidthModulus N r r (q : ℝ) := by
  dsimp only
  let w := (gamma0CuspTrueWidth N r : ℝ)
  let freq := |cuspFourierFrequency 1 n|
  let p := freq/w
  let ρ := spectralFrequencyTestProfile p F
  let σ (y : ℝ) := ρ (w*y)
  let C := gamma0TrueWidthModulus N r r (q : ℝ)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hfreq : 0 < freq := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
  have hp : 0 < p := div_pos hfreq hw
  have hpF : tsupport F ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le (hSF hx).1
  have hρ : ContDiff ℝ ∞ ρ := spectralFrequencyTestProfile_contDiff p F hF hpF
  have hcρ : HasCompactSupport ρ := spectralFrequencyTestProfile_compact p hp F hcF
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) :=
    fun _ hy => (div_pos hA hp).trans_le
      (spectralFrequencyTestProfile_support_lower p hp F (fun _ hx => (hSF hx).1) hy)
  have hC : 0 < C := gamma0TrueWidthModulus_pos N r r (Nat.cast_pos.mpr (NeZero.pos q))
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hi : Integrable (cuspWeylOrbitalIntegrand 1 n n σ σ C hC.ne') := by
    let D := gamma0TrueWidthModulus N r r (((q : ℤ) : ℝ))
    have hD : D ≠ 0 := gamma0TrueWidthModulus_ne_zero N r r (by exact_mod_cast hq)
    have he : D = C := by simp only [D,C,Int.cast_natCast]
    have hcongr (x y : ℝ) (h : x = y) (hx : x ≠ 0) (hy : y ≠ 0) :
        cuspWeylOrbitalIntegrand 1 n n σ σ x hx = cuspWeylOrbitalIntegrand 1 n n σ σ y hy := by
      subst y
      rfl
    have h := cuspWeylOrbitalIntegrand_trueWidth_integrable N r r n n ρ ρ hρ hρ hcρ hcρ hpρ hpρ (q : ℤ) hq
    change Integrable (cuspWeylOrbitalIntegrand 1 n n σ σ D hD) at h
    rwa [hcongr D C he hD hC.ne'] at h
  have hS : Function.support σ ⊆ Icc (A/freq) (2*(A/freq)) :=
    spectralFrequencyTestProfile_scaled_comparable_support F hfreq hw hSF
  have hM (y : ℝ) (_ : y ∈ Icc (A/freq) (2*(A/freq))) :
      ‖σ y‖ ≤ Real.sqrt y*Real.sqrt w :=
    spectralFrequencyTestProfile_scaled_norm_le F h01 p hw y
  change ‖gamma0TrueWidthBesselOrbital N r r q n n ρ ρ‖ ≤ 8*w/C
  rw [← gamma0TrueWidthOrbitalKernel_nonzero_bessel N r r q n n hn hn ρ ρ hρ hρ hcρ hcρ hpρ hpρ]
  calc
    _ ≤ 8*Real.sqrt w*Real.sqrt w/C :=
      cuspWeylOrbitalKernel_comparable_height_norm_le 1 n n σ σ (div_pos hA hfreq) hC
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS hS hM hM
        (weylPlanarDensity_integrable_of_orbital 1 n n σ σ C hC.ne' hi)
    _ = _ := by rw [mul_assoc,← sq,Real.sq_sqrt hw.le]

end ArtinMatthews
