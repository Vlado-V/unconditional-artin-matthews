module

public import ArtinMatthews.SpectralInfinityPrincipalDyadicOrbitBessel
public import ArtinMatthews.SpectralFiniteDyadicCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The actual principal-series coefficients satisfy a uniform
all-height cutoff bound, with the explicit frequency-overlap term. -/

noncomputable section
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

theorem gamma0Infinity_principal_cutoff_orbit_bessel :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (N : ℕ) [NeZero N]
      (u : Finset (Gamma0AllHeightSpectralIndex N)) (v : Finset ι)
      (α : ι → ℂ) (n : ι → ℤ) (_ : Function.Injective n) (hn0 : ∀ j, n j ≠ 0)
      {R B Y : ℝ} (_ : 1 ≤ R) (_ : 0 < B) (hY : 0 < Y) (_ : Y < 1/16/B)
      (_ : ∀ j, |cuspFourierFrequency 1 (n j)| ≤ B)
      (_ : ∀ i ∈ u, 1/4 ≤ gamma0AllHeightGradientSpectralValue N i)
      (_ : ∀ i ∈ u, 1+|Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)| ≤ R),
      let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
      let t (i : Gamma0AllHeightSpectralIndex N) := Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)
      (∑ i ∈ u, ‖∑ j ∈ v, star (α j)*gamma0CuspBesselAmplitude N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j))‖^2/Real.cosh (Real.pi*t i)) ≤
        C*(R^2+B*R/(N : ℝ))*(∑ j ∈ v, ‖α j‖^2) := by
  classical
  obtain ⟨C,hC,hDyad⟩ := gamma0Infinity_principal_dyadic_orbit_bessel
  refine ⟨2*C,by positivity,?_⟩
  intro ι N inst u v α n hn hn0 R B Y hR hB hY hYB hfreq hprincipal hcut
  dsimp only
  let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
  let t (i : Gamma0AllHeightSpectralIndex N) := Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)
  let τ (i : Gamma0AllHeightSpectralIndex N) := 1+|t i|
  let f (i : Gamma0AllHeightSpectralIndex N) :=
    ‖∑ j ∈ v, star (α j)*gamma0CuspBesselAmplitude N i 1 Y hY (nN j)
      (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j))‖^2/Real.cosh (Real.pi*t i)
  let A := ∑ j ∈ v, ‖α j‖^2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hτ (i : Gamma0AllHeightSpectralIndex N) (hi : i ∈ u) : 1 ≤ τ i ∧ τ i ≤ R :=
    ⟨by dsimp only [τ]; linarith [abs_nonneg (t i)],hcut i hi⟩
  have hf (i : Gamma0AllHeightSpectralIndex N) (_ : i ∈ u) : 0 ≤ f i :=
    div_nonneg (sq_nonneg _) (Real.cosh_pos _).le
  have hWin (k : ℕ) : (∑ i ∈ u.filter (fun i => (2 : ℝ)^k ≤ τ i ∧ τ i ≤ 2*(2 : ℝ)^k), f i) ≤
      C*(((2 : ℝ)^k)^2+(B/(N : ℝ))*(2 : ℝ)^k)*A := by
    let T : ℝ := 2^k
    let U := u.filter (fun i => T ≤ τ i ∧ τ i ≤ 2*T)
    have hT : 1 ≤ T := one_le_pow₀ (by norm_num)
    have hY' : Y < T/16/B := hYB.trans_le
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hT (by norm_num)) hB.le)
    have h := hDyad N U v α n hn hn0 (T := T) (B := B) (Y := Y)
      (by linarith only [hT]) hB hY hY' hfreq
      (fun i hi => hprincipal i (Finset.mem_filter.mp hi).1)
      (fun i hi => (Finset.mem_filter.mp hi).2)
    change (∑ i ∈ U, f i) ≤ C*(T^2+B*T/(N : ℝ))*A at h
    rw [show B*T/(N : ℝ) = (B/(N : ℝ))*T by ring] at h
    exact h
  have h := spectral_nonneg_dyadic_cutoff_sum_le u τ f hR (B := B/(N : ℝ)) (by positivity)
    hC.le hA hτ hf hWin
  change (∑ i ∈ u, f i) ≤ (2*C)*(R^2+B*R/(N : ℝ))*A
  rwa [show (B/(N : ℝ))*R = B*R/(N : ℝ) by ring] at h

end ArtinMatthews
