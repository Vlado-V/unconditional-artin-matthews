module

public import ArtinMatthews.SpectralMixedCuspAmbientCompactMoment
public import ArtinMatthews.SpectralMixedCuspExceptionalWeil
public import ArtinMatthews.SpectralCompactExceptionalForcing
public import ArtinMatthews.SpectralHeatSpectralPairing


set_option backward.privateInPublic true
@[expose] public section

/-! A nonzero Fourier mode of a normalized ambient eigenvector at 1/s
obeys the actual compact Weil exponent bound. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0MixedCusp_ambient_unit_value_ge_three_sixteenths_of_amplitude
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (eig : ℝ) (heig₀ : 0 ≤ eig) (v : Gamma0RegionL2 (r*s))
    (hG : gamma0Green (r*s) v = (((eig+1)⁻¹ : ℝ) : ℂ) • v) (hv : ‖v‖ = 1)
    (n : ℤ) (hn : n ≠ 0)
    (hAmp : gamma0AmbientBesselAmplitude (r*s) eig heig₀ v hG (gamma0CuspOneOver s)
      ((gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero (r*s) (gamma0CuspOneOver s) hn) ≠ 0) :
    3/16 ≤ eig := by
  by_cases heig : eig ≤ 1/4
  · let N := r*s
    let b := gamma0CuspOneOver s
    let w := (gamma0CuspTrueWidth N b : ℝ)
    let q := |cuspFourierFrequency 1 n|
    let κ := Real.sqrt (1/4-eig)
    let c := Real.exp (-Real.exp 1)/16
    let amp := gamma0AmbientBesselAmplitude N eig heig₀ v hG b
      ((gamma0CuspFrequencyStep N b : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N b hn)
    let W := c^2*‖(Real.sqrt w : ℂ)*amp‖^2
    have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b)
    have hq : 0 < q := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
    have hc : 0 < c := div_pos (Real.exp_pos _) (by norm_num)
    have hAmp' : 0 < ‖(Real.sqrt w : ℂ)*amp‖ :=
      norm_pos_iff.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hw).ne') hAmp)
    have hW : 0 < W := mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos hAmp')
    have hκ₀ : 0 ≤ κ := Real.sqrt_nonneg _
    have hκ₁ : κ ≤ 1/2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    have hκ : κ ≤ 1/4 := spectral_compact_exceptional_growth_forces_quarter hW hq (by
      intro ε hε _
      obtain ⟨D,hD,hWeil⟩ := spectralKloostermanDiagSum_weil hε
      let C := 8*D*(n.natAbs.divisors.card : ℝ)*Real.sqrt (Nat.gcd N n.natAbs : ℝ)/(N : ℝ)
      have hC : 0 ≤ C := by dsimp only [C]; positivity
      refine ⟨C,hC,?_⟩
      intro A hA hA₁
      obtain ⟨F,hF,hcF,hSF,h01,hOne⟩ := spectralKExceptionalPhysicalTest_exists hA
      let K := ∫ x : ℝ, (F x : ℂ)*schlafliBesselK (κ : ℂ) x ∂spectralKLPhysicalMeasure
      have hK : c*A^(-κ) ≤ ‖K‖ :=
        spectralKExceptionalPhysicalTest_transform_lower F hF.continuous hA hA₁
          hSF (fun x => (h01 x).1) hOne hκ₀ hκ₁
      have hPow : (A^(-κ))^2 = A^(-2*κ) := by
        rw [← Real.rpow_mul_natCast hA.le]
        congr 1
        push_cast
        ring
      have hK₂ : c^2*A^(-2*κ) ≤ ‖K‖^2 := by
        rw [← hPow,← mul_pow]
        exact pow_le_pow_left₀ (mul_nonneg hc.le (Real.rpow_nonneg hA.le _)) hK 2
      have h := gamma0MixedCusp_ambient_compact_moment_le r s hcop eig heig₀ v hG
        n hn F hF hcF hA hSF h01
      dsimp only at h
      rw [spectralComplexSqrt_quarter_sub_nonneg eig heig,hv,one_pow,mul_one] at h
      have hS := hWeil N n hn (q/A) (div_pos hq hA)
      calc
        _ = (c^2*A^(-2*κ))*‖(Real.sqrt w : ℂ)*amp‖^2 := by dsimp only [W]; ring
        _ ≤ ‖K‖^2*‖(Real.sqrt w : ℂ)*amp‖^2 :=
          mul_le_mul_of_nonneg_right hK₂ (sq_nonneg _)
        _ ≤ 1+8*spectralKloostermanDiagSum N n (q/A) := by rw [mul_comm]; exact h
        _ ≤ 1+8*(D*(q/A)^ε*(n.natAbs.divisors.card : ℝ)*Real.sqrt (Nat.gcd N n.natAbs : ℝ)*
              Real.sqrt (q/A)/(N : ℝ)) := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hS (by norm_num))
        _ = _ := by dsimp only [C]; ring)
    have hsq := (sq_le_sq₀ hκ₀ (by norm_num : (0 : ℝ) ≤ 1/4)).mpr hκ
    dsimp only [κ] at hsq
    rw [Real.sq_sqrt (sub_nonneg.mpr heig)] at hsq
    linarith
  · linarith

theorem gamma0MixedCusp_residual_value_ge_three_sixteenths_of_rho
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s) (l : Ici (0 : ℝ))
    (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace (r*s) l)))
    (n : ℤ) (hn : n ≠ 0)
    (hRho : gamma0ResidualABLSourceRho (r*s) l j (gamma0CuspOneOver s) n hn ≠ 0) :
    3/16 ≤ (l : ℝ) := by
  let v := (gamma0ResidualEigenbasis (r*s) l j).val
  have hv : ‖v‖ = 1 := (gamma0ResidualEigenbasis (r*s) l).orthonormal.norm_eq_one j
  apply gamma0MixedCusp_ambient_unit_value_ge_three_sixteenths_of_amplitude r s hcop
    (l : ℝ) l.property v (gamma0ResidualEigenbasis_green (r*s) l j) hv n hn
  intro h
  apply hRho
  exact (congrArg
    (spectralABLRhoFromNative (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ) |(n : ℝ)|) h).trans
      (by simp [spectralABLRhoFromNative])

theorem gamma0MixedCusp_residual_zero_energy_rho (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s)
    (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace (r*s) 0)))
    (n : ℤ) (hn : n ≠ 0) :
    gamma0ResidualABLSourceRho (r*s) ⟨0,Set.mem_Ici.mpr le_rfl⟩ j (gamma0CuspOneOver s) n hn = 0 := by
  by_contra h
  have hp := gamma0MixedCusp_residual_value_ge_three_sixteenths_of_rho r s hcop ⟨0,Set.mem_Ici.mpr le_rfl⟩ j n hn h
  norm_num at hp

end ArtinMatthews
