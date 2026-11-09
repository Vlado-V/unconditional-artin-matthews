module

public import ArtinMatthews.SpectralMixedCuspPhysicalBessel
public import ArtinMatthews.SpectralAmbientBesselAmplitude


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact same-cusp Weil norm controls the nonzero Fourier
mode of every ambient eigenvector, including residual ones. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0MixedCusp_ambient_compact_moment_le (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (eig : ℝ) (heig : 0 ≤ eig) (v : Gamma0RegionL2 (r*s))
    (hG : gamma0Green (r*s) v = (((eig+1)⁻¹ : ℝ) : ℂ) • v)
    (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    {A : ℝ} (hA : 0 < A) (hSF : tsupport F ⊆ Icc A (2*A)) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    let N := r*s
    let b := gamma0CuspOneOver s
    let w := (gamma0CuspTrueWidth N b : ℝ)
    let q := |cuspFourierFrequency 1 n|
    let nN := (gamma0CuspFrequencyStep N b : ℤ)*n
    let amp := gamma0AmbientBesselAmplitude N eig heig v hG b nN
      (gamma0CuspFrequencyStep_mul_ne_zero N b hn)
    let K := ∫ x : ℝ, (F x : ℂ)*schlafliBesselK (Complex.sqrt (1/4-(eig : ℂ))) x ∂spectralKLPhysicalMeasure
    ‖(Real.sqrt w : ℂ)*amp‖^2 * ‖K‖^2 ≤
      (1+8*spectralKloostermanDiagSum N n (q/A))*‖v‖^2 := by
  dsimp only
  let N := r*s
  let b := gamma0CuspOneOver s
  let w := (gamma0CuspTrueWidth N b : ℝ)
  let q := |cuspFourierFrequency 1 n|
  let p := q/w
  let nN := (gamma0CuspFrequencyStep N b : ℤ)*n
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
  have hq : 0 < q := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
  have hp : 0 < p := div_pos hq hw
  let Y := (A/p)/2
  have hY : 0 < Y := half_pos (div_pos hA hp)
  let ν := Complex.sqrt (1/4-(eig : ℂ))
  let amp := gamma0AmbientBesselAmplitude N eig heig v hG b nN
    (gamma0CuspFrequencyStep_mul_ne_zero N b hn)
  let K := ∫ x : ℝ, (F x : ℂ)*schlafliBesselK ν x ∂spectralKLPhysicalMeasure
  let ρ := spectralFrequencyTestProfile p F
  have hpF : tsupport F ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le (hSF hx).1
  have hρ : ContDiff ℝ ∞ ρ := spectralFrequencyTestProfile_contDiff p F hF hpF
  have hcρ : HasCompactSupport ρ := spectralFrequencyTestProfile_compact p hp F hcF
  have hLo (y : ℝ) (hy : y ∈ tsupport ρ) : A/p ≤ y :=
    spectralFrequencyTestProfile_support_lower p hp F (fun _ hx => (hSF hx).1) hy
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => (div_pos hA hp).trans_le (hLo y hy)
  have hsρ : tsupport ρ ⊆ Ioi Y := fun y hy => (half_lt_self (div_pos hA hp)).trans_le (hLo y hy)
  let P := gamma0FourierPoincareTest N b nN ρ hρ hcρ hpρ
  have hFreq : |cuspFourierFrequency (N : ℝ) nN| = p :=
    (eq_div_iff hw.ne').mpr (cuspFourierFrequency_abs_trueWidth N b n)
  have hPair : inner ℂ P v = (2*(N : ℂ))*amp*K := by
    have h := gamma0FourierPoincareTest_ambient_inner N eig heig v hG b nN
      (gamma0CuspFrequencyStep_mul_ne_zero N b hn) Y hY ρ hρ hcρ hpρ hsρ
    rw [hFreq,spectralFrequencyTestProfile_transform p hp F ν Y hY.le hsρ] at h
    exact h
  have hNorm := gamma0MixedSameCusp_comparable_diagonal_norm_le r s hcop n hn F hF hcF
    hA hSF h01 ρ hρ hcρ hpρ rfl
  change w*‖P‖^2 ≤ (2*(N : ℝ))^2*(1+8*spectralKloostermanDiagSum N n (q/A)) at hNorm
  have hSq : ‖inner ℂ P v‖^2 ≤ ‖P‖^2*‖v‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (inner ℂ P v)) (norm_inner_le_norm (𝕜 := ℂ) P v) 2
  have hfac : ‖(2*(N : ℂ))‖ = 2*(N : ℝ) := by
    simp [norm_mul,Complex.norm_natCast]
  have hAfac : ‖(Real.sqrt w : ℂ)*amp‖^2 = w*‖amp‖^2 := by
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hw.le]
  change ‖(Real.sqrt w : ℂ)*amp‖^2 * ‖K‖^2 ≤ _
  apply (mul_le_mul_iff_of_pos_left (show 0 < (2*(N : ℝ))^2 by positivity)).mp
  calc
    _ = w*‖inner ℂ P v‖^2 := by
      rw [hPair,hAfac,norm_mul ((2*(N : ℂ))*amp) K,
        norm_mul (2*(N : ℂ)) amp,hfac]
      ring
    _ ≤ w*(‖P‖^2*‖v‖^2) := mul_le_mul_of_nonneg_left hSq hw.le
    _ = (w*‖P‖^2)*‖v‖^2 := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hNorm (sq_nonneg ‖v‖)
      exact h.trans_eq (by ring)

end ArtinMatthews
