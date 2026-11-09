module

public import ArtinMatthews.SpectralMixedSameCuspDiagonalGramBound
public import ArtinMatthews.SpectralKExceptionalPhysicalTest
public import ArtinMatthews.SpectralCuspTrueWidthPhysicalMoment


set_option backward.privateInPublic true
@[expose] public section

/-! A full compact Poincare norm bound and its finite cuspidal Bessel
consequence for one actual physical profile at the mixed source cusp. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators

namespace ArtinMatthews

theorem gamma0MixedSameCusp_comparable_diagonal_norm_le (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    {A : ℝ} (hA : 0 < A) (hSF : tsupport F ⊆ Icc A (2*A)) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hProfile : ρ = spectralFrequencyTestProfile
      (|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) F) :
    let N := r*s
    let a := gamma0CuspOneOver s
    let w := (gamma0CuspTrueWidth N a : ℝ)
    let d := gamma0CuspFrequencyStep N a
    let P := gamma0FourierPoincareTest N a ((d : ℤ)*n) ρ hρ hcρ hpρ
    w*‖P‖^2 ≤ (2*(N : ℝ))^2*(1+8*spectralKloostermanDiagSum N n (|cuspFourierFrequency 1 n|/A)) := by
  dsimp only
  let N := r*s
  let a := gamma0CuspOneOver s
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let d := gamma0CuspFrequencyStep N a
  let nN := (d : ℤ)*n
  let freq := |cuspFourierFrequency 1 n|
  let p := freq/w
  let S := spectralKloostermanDiagSum N n (freq/A)
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hp : 0 < p := div_pos (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)) hw
  let ψ := cuspFourierTestSeed (N : ℝ) hN nN ρ hρ hcρ hpρ
  let P := gamma0FourierPoincareTest N a nN ρ hρ hcρ hpρ
  let G := gamma0PositiveGeometricSum N a a ψ ψ
  let M := ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure
  have hM : M ≤ 1 := spectralKExceptionalPhysicalTest_mass_le F hF.continuous hA hSF h01
  have hMass : cuspFourierHeightPairing ρ ρ = M := by
    rw [hProfile]
    exact spectralFrequencyTestProfile_height_mass p hp F
  have hGeom : ‖G‖ ≤ 8*(d : ℝ)^2*w*S :=
    gamma0MixedSameCusp_comparable_diagonal_positive_norm_le r s hcop n hn F hF hcF hA hSF h01
      ρ hρ hcρ hpρ hProfile
  have hGram : inner ℂ P P = ((4*(d : ℝ)*(N : ℝ)*M : ℝ) : ℂ)+4*G := by
    have h := gamma0FourierPoincareTest_sameCusp_gram N a n n ρ ρ hρ hρ hcρ hcρ hpρ hpρ
    change inner ℂ P P = (if n = n then ((4*(d : ℝ)*(N : ℝ)*cuspFourierHeightPairing ρ ρ : ℝ) : ℂ)
      else 0)+4*G at h
    rw [ite_eq_left (show n=n from rfl),hMass] at h
    exact h
  have hP : ‖P‖^2 = 4*(d : ℝ)*(N : ℝ)*M+4*G.re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ),hGram]
    change (((4*(d : ℝ)*(N : ℝ)*M : ℝ) : ℂ)+4*G).re = _
    rw [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  have hdw : (d : ℝ)*w = (N : ℝ) := by
    rw [mul_comm]
    change (gamma0CuspTrueWidth N a : ℝ)*(gamma0CuspFrequencyStep N a : ℝ) = (N : ℝ)
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N a
  change w*‖P‖^2 ≤ (2*(N : ℝ))^2*(1+8*S)
  rw [hP]
  calc
    _ ≤ w*(4*(d : ℝ)*(N : ℝ)*1+4*(8*(d : ℝ)^2*w*S)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hM (by positivity))
        (mul_le_mul_of_nonneg_left ((Complex.re_le_norm G).trans hGeom) (by norm_num))) hw.le
    _ = 4*((d : ℝ)*w)*(N : ℝ)+32*((d : ℝ)*w)^2*S := by ring
    _ = _ := by rw [hdw]; ring

theorem gamma0MixedSameCusp_comparable_physical_finite_bessel (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (u : Finset (Gamma0AllHeightSpectralIndex (r*s)))
    (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y)
    (hYA : Y < A/(|cuspFourierFrequency 1 n|/
      (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)))
    (hSF : tsupport F ⊆ Icc A (2*A)) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    gamma0CuspPhysicalBesselMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn F ≤
      1+8*spectralKloostermanDiagSum (r*s) n (|cuspFourierFrequency 1 n|/A) := by
  let N := r*s
  let a := gamma0CuspOneOver s
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let freq := |cuspFourierFrequency 1 n|
  let p := freq/w
  have hN : 0 < ((r*s : ℕ) : ℝ) := Nat.cast_pos.mpr (NeZero.pos (r*s))
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hp : 0 < p := div_pos (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)) hw
  let ρ := spectralFrequencyTestProfile p F
  have hpF : tsupport F ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le (hSF hx).1
  have hρ : ContDiff ℝ ∞ ρ := spectralFrequencyTestProfile_contDiff p F hF hpF
  have hcρ : HasCompactSupport ρ := spectralFrequencyTestProfile_compact p hp F hcF
  have hLo (y : ℝ) (hy : y ∈ tsupport ρ) : A/p ≤ y :=
    spectralFrequencyTestProfile_support_lower p hp F (fun _ hx => (hSF hx).1) hy
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => (div_pos hA hp).trans_le (hLo y hy)
  have hsρ : tsupport ρ ⊆ Ioi Y := fun y hy => hYA.trans_le (hLo y hy)
  have hPNorm := gamma0MixedSameCusp_comparable_diagonal_norm_le r s hcop n hn F hF hcF
    hA hSF h01 ρ hρ hcρ hpρ rfl
  have hB := gamma0CuspPhysicalBesselMoment_le_scaled_norm (r*s) u (gamma0CuspOneOver s)
    Y hY n hn F ρ hρ hcρ hpρ hsρ rfl
  dsimp only at hB hPNorm
  exact (mul_le_mul_iff_of_pos_left (show 0 < (2*((r*s : ℕ) : ℝ))^2 by positivity)).mp
    (hB.trans hPNorm)

end ArtinMatthews
