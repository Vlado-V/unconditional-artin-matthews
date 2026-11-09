module

public import ArtinMatthews.SpectralInfinityCommonPhysicalOrbitBessel
public import ArtinMatthews.SpectralABLExceptionalCompactDensity


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed compact real-order K profile controls the first-factor
complementary cusp packet at infinity. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0InfinityCuspPacketAmplitude {ι : Type*} (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (v : Finset ι)
    (α : ι → ℂ) (n : ι → ℤ) (hn : ∀ j, n j ≠ 0) (Y : ℝ) (hY : 0 < Y) : ℂ :=
  ∑ j ∈ v, star (α j)*gamma0CuspBesselAmplitude N i 1 Y hY
    ((gamma0CuspFrequencyStep N 1 : ℤ)*n j) (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn j))

theorem gamma0Infinity_complementary_packet_orbit_bessel :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (N : ℕ) [NeZero N]
      (u : Finset (Gamma0AllHeightSpectralIndex N)) (v : Finset ι)
      (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n) (hn₀ : ∀ j, n j ≠ 0)
      {B Y : ℝ}, 0 < B → ∀ hY : 0 < Y,
      Y < (1/4)/B → (∀ j, |cuspFourierFrequency 1 (n j)| ≤ B) →
      (∀ i ∈ u, gamma0AllHeightGradientSpectralValue N i ≤ 1/4) →
      (∑ i ∈ u, ‖gamma0InfinityCuspPacketAmplitude N i v α n hn₀ Y hY‖^2/
        Real.cos (Real.pi*Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i))) ≤
        C*(1+B/(N : ℝ))*(∑ j ∈ v, ‖α j‖^2) := by
  let A : ℝ := 1/4
  let c := Real.exp (-Real.exp 1)/16
  let e := Real.cos (Real.pi/4)
  have hA : 0 < A := by norm_num [A]
  have hc : 0 < c := by dsimp only [c]; positivity
  have he : 0 < e := by dsimp only [e]; rw [Real.cos_pi_div_four]; positivity
  have hE : 0 < c^2*e := by positivity
  obtain ⟨F,hF,hcF,hSupp,h01,hOne⟩ := spectralKExceptionalPhysicalTest_exists hA
  have hMass := spectralKExceptionalPhysicalTest_mass_le F hF.continuous hA hSupp h01
  refine ⟨48/(c^2*e),by positivity,?_⟩
  intro ι N inst u v α n hn hn₀ B Y hB hY hYB hfreq hEig
  let W (i : Gamma0AllHeightSpectralIndex N) := gamma0InfinityCuspPacketAmplitude N i v α n hn₀ Y hY
  let κ (i : Gamma0AllHeightSpectralIndex N) := Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i)
  let K (i : Gamma0AllHeightSpectralIndex N) :=
    ∫ x : ℝ, (F x : ℂ)*schlafliBesselK (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))) x
      ∂spectralKLPhysicalMeasure
  let M := ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure
  let S := ∑ j ∈ v, ‖α j‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hP := gamma0Infinity_common_physical_test_orbit_bessel N u v α n hn hn₀ F hF hcF hA hB hY hYB
    (fun _ hx => (hSupp hx).1) hfreq
  change (∑ i ∈ u, ‖K i*W i‖^2) ≤ 6*(1+2*B/((N : ℝ)*A))*(M*S) at hP
  have hK (i : Gamma0AllHeightSpectralIndex N) (hi : i ∈ u) : c ≤ ‖K i‖ := by
    have hκ : 0 ≤ κ i := Real.sqrt_nonneg _
    have hκ₁ : κ i ≤ 1/2 := (gamma0Cuspidal_complementary_parameter_le_quarter N i).trans (by norm_num)
    have hPow : 1 ≤ A^(-κ i) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow_of_nonpos hA (by norm_num [A] : A ≤ 1) (neg_nonpos.mpr hκ)
    dsimp only [K]
    rw [spectralComplexSqrt_quarter_sub_nonneg _ (hEig i hi)]
    exact (le_mul_of_one_le_right hc.le hPow).trans
      (spectralKExceptionalPhysicalTest_transform_lower F hF.continuous hA (by norm_num [A])
        hSupp (fun x => (h01 x).1) hOne hκ hκ₁)
  change (∑ i ∈ u, ‖W i‖^2/Real.cos (Real.pi*κ i)) ≤ (48/(c^2*e))*(1+B/(N : ℝ))*S
  apply (mul_le_mul_iff_of_pos_left hE).mp
  calc
    _ ≤ ∑ i ∈ u, ‖K i*W i‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hCos : e ≤ Real.cos (Real.pi*κ i) := gamma0Cuspidal_complementary_cos_lower N i
      rw [norm_mul,mul_pow]
      calc
        _ = (e/Real.cos (Real.pi*κ i))*(c^2*‖W i‖^2) := by ring
        _ ≤ c^2*‖W i‖^2 := mul_le_of_le_one_left (by positivity) ((div_le_one (he.trans_le hCos)).mpr hCos)
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le (hK i hi) 2) (sq_nonneg _)
    _ ≤ 6*(1+2*B/((N : ℝ)*A))*(M*S) := hP
    _ ≤ 6*(1+2*B/((N : ℝ)*A))*S := by
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hS hMass) (by positivity)
    _ ≤ (48*(1+B/(N : ℝ)))*S := by
      apply mul_le_mul_of_nonneg_right _ hS
      have hEq : 2*B/((N : ℝ)*A) = 8*(B/(N : ℝ)) := by
        dsimp only [A]
        ring
      rw [hEq]
      linarith
    _ = _ := by field_simp [hE.ne']

end ArtinMatthews
