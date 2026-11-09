module

public import ArtinMatthews.SpectralWeylOrbitalFrequency


set_option backward.privateInPublic true
@[expose] public section

/-! Actual nonzero-frequency orbital J/K transform, with the integer sign
sector, frequency argument, and literal positive-modulus prefactor. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def spectralWeylIntegerSignMultiplier (m n : ℤ) (r X : ℝ) : ℂ :=
  if 0 < m*n then spectralWeylJMultiplier r X else spectralWeylKMultiplier r X

theorem spectralWeyl_frequency_sign_sq {u : ℝ} (hu : u ≠ 0) : (u/|u|)^2 = 1 := by
  rw [div_pow,sq_abs,div_self (pow_ne_zero 2 hu)]

theorem spectralWeyl_frequency_sign_product {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (u/|u|)*(v/|v|) = if 0 < u*v then 1 else -1 := by
  rw [div_mul_div_comm,← abs_mul]
  split_ifs with h
  · rw [abs_of_pos h,div_self h.ne']
  · have hn : u*v < 0 := lt_of_le_of_ne (le_of_not_gt h) (mul_ne_zero hu hv)
    rw [abs_of_neg hn,div_neg,div_self hn.ne]

theorem spectralWeyl_cusp_frequency_product_pos {w : ℝ} (hw : 0 < w) (m n : ℤ) :
    0 < cuspFourierFrequency w m*cuspFourierFrequency w n ↔ 0 < m*n := by
  have he : cuspFourierFrequency w m*cuspFourierFrequency w n =
      (2*Real.pi/w)^2*((m : ℝ)*(n : ℝ)) := by
    unfold cuspFourierFrequency
    ring_nf
  rw [he,mul_pos_iff_of_pos_left (sq_pos_of_pos (div_pos (mul_pos two_pos Real.pi_pos) hw))]
  exact_mod_cast (Iff.rfl : 0 < m*n ↔ 0 < m*n)

theorem cuspWeylOrbitalKernel_nonzero_spectral (N : ℕ) [NeZero N] (m n : ℤ)
    (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hη : Continuous η) (hcη : HasCompactSupport η) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {C : ℝ} (hC : 0 < C)
    (hI : IntegrableOn (weylPlanarDensity N m n ρ η C) {p : ℝ × ℝ | 0 < p.2}) :
    let a := |cuspFourierFrequency (N : ℝ) m|
    let b := |cuspFourierFrequency (N : ℝ) n|
    let X := Real.sqrt (a*b)*(2/C)
    cuspWeylOrbitalKernel N m n ρ η C hC.ne' =
      ((Real.sqrt (a*b)/C^2 : ℝ) : ℂ)*
        (∫ r : ℝ, spectralWeylIntegerSignMultiplier m n r X*
          spectralKLPhysicalAnalysisIntegral (spectralKLHeightPhysicalTest b η) r*
          star (spectralKLPhysicalAnalysisIntegral (spectralKLHeightPhysicalTest a ρ) r)
            ∂spectralKLSpectralMeasure) := by
  dsimp only
  let U := cuspFourierFrequency (N : ℝ) m
  let V := cuspFourierFrequency (N : ℝ) n
  let a := |U|
  let b := |V|
  let X := Real.sqrt (a*b)*(2/C)
  let f := spectralKLHeightPhysicalTest b η
  let g := spectralKLHeightPhysicalTest a ρ
  have hw : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hU : U ≠ 0 := cuspFourierFrequency_ne_zero (N : ℝ) hw m hm
  have hV : V ≠ 0 := cuspFourierFrequency_ne_zero (N : ℝ) hw n hn
  have ha : 0 < a := abs_pos.mpr hU
  have hb : 0 < b := abs_pos.mpr hV
  have hX : 0 < X := mul_pos (Real.sqrt_pos.mpr (mul_pos ha hb)) (div_pos two_pos hC)
  have hU2 : (U/a)^2 = 1 := spectralWeyl_frequency_sign_sq hU
  have hV2 : (V/b)^2 = 1 := spectralWeyl_frequency_sign_sq hV
  have hsign : (U/a)*(V/b) = if 0 < m*n then 1 else -1 := by
    rw [spectralWeyl_frequency_sign_product hU hV]
    have hp : 0 < U*V ↔ 0 < m*n := spectralWeyl_cusp_frequency_product_pos hw m n
    by_cases hmn : 0 < m*n
    · rw [ite_eq_left (hp.mpr hmn),ite_eq_left hmn]
    · rw [ite_eq_right (fun h => hmn (hp.mp h)),ite_eq_right hmn]
  obtain ⟨hf,hfc,hfp⟩ := spectralKLHeightPhysicalTest_properties hb η hη hcη hpη
  obtain ⟨hg,hgc,hgp⟩ := spectralKLHeightPhysicalTest_properties ha ρ hρ hcρ hpρ
  change cuspWeylOrbitalKernel N m n ρ η C hC.ne' =
    ((Real.sqrt (a*b)/C^2 : ℝ) : ℂ)*
      (∫ r : ℝ, spectralWeylIntegerSignMultiplier m n r X*spectralKLPhysicalAnalysisIntegral f r*
        star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure)
  rw [cuspWeylOrbitalKernel_frequency_physical N m n ρ η hρ hcρ hpρ hη hcη hpη ha hb hC hI]
  congr 1
  change spectralWeylPhysicalBilinear (U/a) (V/b) f g X = _
  by_cases hmn : 0 < m*n
  · have hUV : (U/a)*(V/b) = 1 := by rwa [ite_eq_left hmn] at hsign
    rw [spectralWeylPhysicalBilinear_same_J hX (U/a) (V/b) hU2 hV2 hUV f g hf hfc hfp hg hgc hgp]
    simp only [spectralWeylIntegerSignMultiplier,ite_eq_left hmn]
  · have hUV : (U/a)*(V/b) = -1 := by rwa [ite_eq_right hmn] at hsign
    rw [spectralWeylPhysicalBilinear_opposite_K hX (U/a) (V/b) hU2 hV2 hUV f g hf hfc hfp hg hgc hgp]
    simp only [spectralWeylIntegerSignMultiplier,ite_eq_right hmn]

end ArtinMatthews
