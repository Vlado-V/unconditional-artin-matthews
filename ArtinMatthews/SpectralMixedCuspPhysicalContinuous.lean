module

public import ArtinMatthews.SpectralMixedCuspPhysicalOrbitMass
public import ArtinMatthews.SpectralNativeCompactContinuous


set_option backward.privateInPublic true
@[expose] public section

/-! The same actual compact mixed-cusp profile bounds the continuous
Fourier moment in the normalized positive-frequency measure. -/

noncomputable section
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0MixedCusp_physical_continuous_moment (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y)
    (hYA : Y < A/(|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)))
    (hSF : tsupport F ⊆ Ici A) :
    let N := r*s
    let b := gamma0CuspOneOver s
    let K (t : ℝ) := ∫ x : ℝ, (F x : ℂ)*schlafliBesselK ((t : ℂ)*Complex.I) x ∂spectralKLPhysicalMeasure
    let C (t : ℝ) := ∑ i : Gamma0EisensteinCuspClasses N,
      ‖gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N i)
        b Y hY n hn (eisensteinCriticalPoint t)*K t‖^2
    Integrable C gamma0EisensteinSpectralMeasure ∧
      (∫ t, C t ∂gamma0EisensteinSpectralMeasure) ≤
        6*(1+2*|cuspFourierFrequency 1 n|/((N : ℝ)*A))*
          (∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure) := by
  dsimp only
  let N := r*s
  let b := gamma0CuspOneOver s
  let w := (gamma0CuspTrueWidth N b : ℝ)
  let q := |cuspFourierFrequency 1 n|
  let p := q/w
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
  have hq : 0 < q := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
  have hp : 0 < p := div_pos hq hw
  let ρ := spectralFrequencyTestProfile p F
  have hpF : tsupport F ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le (hSF hx)
  have hρ : ContDiff ℝ ∞ ρ := spectralFrequencyTestProfile_contDiff p F hF hpF
  have hcρ : HasCompactSupport ρ := spectralFrequencyTestProfile_compact p hp F hcF
  have hlo (y : ℝ) (hy : y ∈ tsupport ρ) : A/p ≤ y :=
    spectralFrequencyTestProfile_support_lower p hp F hSF hy
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => (div_pos hA hp).trans_le (hlo y hy)
  have hsρ : tsupport ρ ⊆ Ioi Y := fun y hy => hYA.trans_le (hlo y hy)
  let U := gamma0PrimitiveFourierPoincareTest N b n ρ hρ hcρ hpρ
  let V := gamma0EisensteinAnalysis N U
  let K (t : ℝ) := ∫ x : ℝ, (F x : ℂ)*schlafliBesselK ((t : ℂ)*Complex.I) x ∂spectralKLPhysicalMeasure
  let B (i : Gamma0EisensteinCuspClasses N) (t : ℝ) :=
    gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N i)
      b Y hY n hn (eisensteinCriticalPoint t)*K t
  have hOrder (ν : ℂ) :
      (∫ x in Ioi (0 : ℝ), schlafliBesselK ν x*
        (spectralKLHeightPhysicalTest q (fun y => ρ (w*y)) x/(x : ℂ))) =
      (Real.sqrt w : ℂ)*(∫ x : ℝ, (F x : ℂ)*schlafliBesselK ν x ∂spectralKLPhysicalMeasure) := by
    have hs := (spectral_cusp_width_test_properties w Y hw ρ hρ.continuous hcρ hsρ).2.2
    rw [← cuspBesselTransform_eq_order_integral ν hq (div_pos hY hw) _ hs]
    have h := cuspBesselTransform_positive_dilation ν p Y w hw hY ρ
    have hpw : p*w=q := div_mul_cancel₀ q hw.ne'
    rw [hpw,spectralFrequencyTestProfile_transform p hp F ν Y hY.le hsρ] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hw).ne'), one_mul]
  have hAE (i : Gamma0EisensteinCuspClasses N) :
      (fun t : ℝ => ‖B i t‖^2) =ᵐ[gamma0EisensteinSpectralMeasure]
        fun t => w⁻¹*‖V i t‖^2 := by
    filter_upwards [gamma0PrimitiveAnalysis_fourier_ae N b n hn Y hY Y hY ρ hρ hcρ hpρ hsρ i] with t ht
    change V i t = star (_*∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*
      (spectralKLHeightPhysicalTest q (fun y => ρ (w*y)) x/(x : ℂ))) at ht
    rw [hOrder] at ht
    change ‖B i t‖^2 = w⁻¹*‖V i t‖^2
    rw [ht,norm_star,show _ * ((Real.sqrt w : ℂ) * _) =
      (Real.sqrt w : ℂ) * B i t by dsimp only [B,K]; ring]
    rw [norm_mul (Real.sqrt w : ℂ) (B i t),mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hw.le,← mul_assoc,inv_mul_cancel₀ hw.ne',one_mul]
  have hV (i : Gamma0EisensteinCuspClasses N) :
      Integrable (fun t : ℝ => ‖V i t‖^2) gamma0EisensteinSpectralMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (V i))).mp (Lp.memLp (V i))
  have hI (i : Gamma0EisensteinCuspClasses N) :
      Integrable (fun t : ℝ => ‖B i t‖^2) gamma0EisensteinSpectralMeasure :=
    ((hV i).const_mul w⁻¹).congr (hAE i).symm
  change Integrable (fun t => ∑ i, ‖B i t‖^2) gamma0EisensteinSpectralMeasure ∧ _
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hI i),?_⟩
  have hVeq (i : Gamma0EisensteinCuspClasses N) :
      (∫ t, ‖V i t‖^2 ∂gamma0EisensteinSpectralMeasure) = ‖V i‖^2 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hNormEq : (∫ t, ∑ i, ‖B i t‖^2 ∂gamma0EisensteinSpectralMeasure) = w⁻¹*‖V‖^2 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hI i),PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_congr_ae (hAE i),integral_const_mul,hVeq]
  rw [hNormEq]
  have hNorm := gamma0MixedSameCusp_physical_orbit_norm_le r s hcop n hn F hA hSF ρ hρ hcρ hpρ rfl
  have hA' : ‖V‖ ≤ ‖U‖ := gamma0EisensteinAnalysis_norm_le N U
  have hS : ‖gamma0PrimitiveFourierScale N b‖ = w/(2*(N : ℝ)) := by
    unfold gamma0PrimitiveFourierScale
    exact Complex.norm_of_nonneg (div_nonneg hw.le (by positivity))
  calc
    _ ≤ w⁻¹*‖U‖^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hA' 2) (inv_nonneg.mpr hw.le)
    _ = (w*‖gamma0FourierPoincareTest N b ((gamma0CuspFrequencyStep N b : ℤ)*n)
        ρ hρ hcρ hpρ‖^2)/(2*(N : ℝ))^2 := by
      dsimp only [U]
      rw [gamma0PrimitiveFourierPoincareTest_eq,norm_smul,hS,mul_pow]
      field_simp [hw.ne',hN.ne']
    _ ≤ _ := (div_le_iff₀ (by positivity : 0 < (2*(N : ℝ))^2)).mpr (by
      exact hNorm.trans_eq (mul_comm _ _))

end ArtinMatthews
