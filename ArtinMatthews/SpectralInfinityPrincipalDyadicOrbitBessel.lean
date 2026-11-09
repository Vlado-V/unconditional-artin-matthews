module

public import ArtinMatthews.SpectralKFrameRetainedModes
public import ArtinMatthews.SpectralKFrameTransform
public import ArtinMatthews.SpectralInfinityCommonPhysicalOrbitBessel
public import ArtinMatthews.SpectralGamma0PoincareKL


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine all-height principal-series bound for actual infinity
coefficients. The orbit-overlap argument retains an explicit BT/N term. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped MatrixGroups ContDiff BigOperators

namespace ArtinMatthews

theorem gamma0Infinity_principal_dyadic_orbit_bessel :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (N : ℕ) [NeZero N]
      (u : Finset (Gamma0AllHeightSpectralIndex N)) (v : Finset ι)
      (α : ι → ℂ) (n : ι → ℤ) (_ : Function.Injective n) (hn0 : ∀ j, n j ≠ 0)
      {T B Y : ℝ} (_ : (1/2 : ℝ) ≤ T) (_ : 0 < B) (hY : 0 < Y)
      (_ : Y < T/16/B)
      (_ : ∀ j, |cuspFourierFrequency 1 (n j)| ≤ B)
      (_ : ∀ i ∈ u, 1/4 ≤ gamma0AllHeightGradientSpectralValue N i)
      (_ : ∀ i ∈ u, let t := Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)
        T ≤ 1+|t| ∧ 1+|t| ≤ 2*T),
      let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
      let t (i : Gamma0AllHeightSpectralIndex N) := Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)
      (∑ i ∈ u, ‖∑ j ∈ v, star (α j)*gamma0CuspBesselAmplitude N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j))‖^2/Real.cosh (Real.pi*t i)) ≤
        C*(T^2+B*T/(N : ℝ))*(∑ j ∈ v, ‖α j‖^2) := by
  let L := spectralKFrameLength
  let P := Real.pi^2*L/5184
  have hL : 0 < L := spectralKFrameLength_pos
  have hP : 0 < P := by dsimp only [P]; positivity
  obtain ⟨ψ,D,_,hψ,hSupp,h01,hOne,hDψ⟩ := spectralKFrameWindow_exists
  obtain ⟨C,hC,hframe⟩ := spectralKFrameLogTest_exists_retained_modes ψ hψ hSupp h01 hOne hDψ
  refine ⟨384*C*L/P,by positivity,?_⟩
  intro ι N inst u v α n hn hn0 T B Y hhalf hB hY hYB hfreq hprincipal hdyad
  dsimp only
  let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
  let eig (i : Gamma0AllHeightSpectralIndex N) := gamma0AllHeightGradientSpectralValue N i
  let t (i : Gamma0AllHeightSpectralIndex N) := Real.sqrt (eig i-1/4)
  let A := ∑ j ∈ v, ‖α j‖^2
  let W (i : Gamma0AllHeightSpectralIndex N) :=
    ∑ j ∈ v, star (α j)*gamma0CuspBesselAmplitude N i 1 Y hY (nN j)
      (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j))
  let Fhat (χ : ℝ → ℝ) (i : Gamma0AllHeightSpectralIndex N) :=
    ∫ x : ℝ, (spectralKFramePhysicalTest ψ χ T x : ℂ)*
      schlafliBesselK (Complex.sqrt (1/4-(eig i : ℂ))) x ∂spectralKLPhysicalMeasure
  let χr (m : ℤ) (x : ℝ) := (cuspFourierPhase L m x).re
  let χi (m : ℤ) (x : ℝ) := (cuspFourierPhase L m x).im
  let E (m : ℤ) (i : Gamma0AllHeightSpectralIndex N) :=
    ‖Fhat (χr m) i*W i‖^2+‖Fhat (χi m) i*W i‖^2
  have hT : 0 < T := by linarith
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨s,hcard,hretained⟩ := hframe T hhalf
  let V := 6*(1+2*B/((N : ℝ)*(T/16)))
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hVeq : T*V = 6*(T+32*B/(N : ℝ)) := by
    dsimp only [V]
    field_simp [hT.ne',hN.ne']
    ring
  have hMoment (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ1 : ∀ x, |χ x| ≤ 1) :
      (∑ i ∈ u, ‖Fhat χ i*W i‖^2) ≤ V*(L*A) := by
    let F := spectralKFramePhysicalTest ψ χ T
    have hF := spectralKFramePhysicalTest_contDiff ψ χ hψ hχ hSupp T hT
    have hcF := spectralKFramePhysicalTest_compact ψ χ hSupp T hT
    have hSF : tsupport F ⊆ Ici (T/16) := fun _ hx =>
      (spectralKFramePhysicalTest_support ψ χ hSupp T hT hx).1
    have h := gamma0Infinity_common_physical_test_orbit_bessel N u v α n hn hn0 F hF hcF
      (by positivity : 0 < T/16) hB hY hYB hSF hfreq
    exact h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (spectralKFramePhysicalTest_mass_le ψ χ hψ hχ hSupp h01 hχ1 T hT) hA) hV)
  have hmode (m : ℤ) : (∑ i ∈ u, E m i) ≤ 2*V*L*A := by
    have hr : ContDiff ℝ ∞ (χr m) := Complex.reCLM.contDiff.comp (cuspFourierPhase_contDiff L m)
    have hi : ContDiff ℝ ∞ (χi m) := Complex.imCLM.contDiff.comp (cuspFourierPhase_contDiff L m)
    have hcr (x : ℝ) : |χr m x| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans_eq (cuspFourierPhase_norm L m x)
    have hci (x : ℝ) : |χi m x| ≤ 1 :=
      (Complex.abs_im_le_norm _).trans_eq (cuspFourierPhase_norm L m x)
    dsimp only [E]
    rw [Finset.sum_add_distrib]
    calc
      _ ≤ V*(L*A)+V*(L*A) := add_le_add (hMoment _ hr hcr) (hMoment _ hi hci)
      _ = _ := by ring
  have htotal : (∑ i ∈ u, ∑ m ∈ s, E m i) ≤ (C*T)*(2*V*L*A) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _m ∈ s, 2*V*L*A := Finset.sum_le_sum (fun m _ => hmode m)
      _ = (s.card : ℝ)*(2*V*L*A) := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hrow (i : Gamma0AllHeightSpectralIndex N) (hi : i ∈ u) :
      (P/T)*(‖W i‖^2/Real.cosh (Real.pi*t i)) ≤ ∑ m ∈ s, E m i := by
    let c (m : ℤ) := fourierCoeffOn spectralKFrameLength_pos
      (fun u => (spectralKFrameLogTest ψ T (t i) u : ℂ)) m
    have hsum : (∑ m ∈ s, E m i) = (L^2*‖W i‖^2)*(∑ m ∈ s, ‖c m‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      have hχ : ‖Fhat (χr m) i‖^2+‖Fhat (χi m) i‖^2 = L^2*‖c m‖^2 := by
        dsimp only [Fhat]
        rw [spectralComplexSqrt_quarter_sub_real (eig i) (hprincipal i hi)]
        exact spectralKFramePhysicalTest_principal_phase_sq ψ hψ hSupp T (t i) hT m
      dsimp only [E]
      rw [norm_mul,norm_mul,mul_pow,mul_pow,← add_mul,hχ]
      ring
    have hR := hretained (t i) (hdyad i hi).1 (hdyad i hi).2
    rw [hsum]
    calc
      _ = (L^2*‖W i‖^2)*(spectralKSquareMoment 0 (t i)/(1296*L*T)) := by
        rw [spectralKSquareMoment_zero]
        dsimp only [P]
        field_simp [hT.ne',hL.ne',(Real.cosh_pos _).ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)
  change (∑ i ∈ u, ‖W i‖^2/Real.cosh (Real.pi*t i)) ≤ (384*C*L/P)*(T^2+B*T/(N : ℝ))*A
  apply (mul_le_mul_iff_of_pos_left (div_pos hP hT)).mp
  calc
    _ ≤ ∑ i ∈ u, ∑ m ∈ s, E m i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hrow
    _ ≤ (C*T)*(2*V*L*A) := htotal
    _ = (12*C*L)*(T+32*B/(N : ℝ))*A := by
      calc
        _ = (2*C*L)*(T*V)*A := by ring
        _ = _ := by rw [hVeq]; ring
    _ ≤ (384*C*L)*(T+B/(N : ℝ))*A := by
      apply mul_le_mul_of_nonneg_right _ hA
      have hLin : T+32*B/(N : ℝ) ≤ 32*(T+B/(N : ℝ)) := by
        rw [mul_add,mul_div_assoc]
        exact add_le_add (by linarith only [hT]) le_rfl
      calc
        _ ≤ (12*C*L)*(32*(T+B/(N : ℝ))) := mul_le_mul_of_nonneg_left hLin (by positivity)
        _ = _ := by ring
    _ = _ := by field_simp [hT.ne',hP.ne',hN.ne']

end ArtinMatthews
