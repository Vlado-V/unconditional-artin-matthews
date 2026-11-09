module

public import ArtinMatthews.SpectralABLNativeRho
public import ArtinMatthews.SpectralPrimitiveContinuousFourier


set_option backward.privateInPublic true
@[expose] public section

/-! The source Whittaker coefficients of the actual continued Eisenstein
series. The finite channel sum and positive-frequency measure are kept
literal. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def gamma0ABLEisensteinRho (N : ℕ) [NeZero N] (a r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (s : ℂ) : ℂ :=
  spectralABLRhoFromNative 1 |(n : ℝ)| (gamma0PrimitiveFourierAmplitude N a r Y hY n hn s)

theorem gamma0ABLEisensteinRho_scale (N : ℕ) [NeZero N] (a r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (s : ℂ) :
    (2*Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLEisensteinRho N a r Y hY n hn s =
      gamma0PrimitiveFourierAmplitude N a r Y hY n hn s := by
  simpa only [gamma0ABLEisensteinRho,Real.sqrt_one,Complex.ofReal_one,one_mul] using
    spectralABLRhoFromNative_scale 1 |(n : ℝ)| (abs_pos.mpr (by exact_mod_cast hn))
      (gamma0PrimitiveFourierAmplitude N a r Y hY n hn s)

theorem gamma0ABLEisensteinRho_factorization_critical_ae (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hsρ : tsupport ρ ⊆ Ioi Y) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      gamma0PrimitiveEisensteinTransform N a r Y hY n (eisensteinCriticalPoint t) ρ =
        (2*Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLEisensteinRho N a r Y hY n hn (eisensteinCriticalPoint t)*
          gamma0PrimitiveKTransform N r Y n ρ (eisensteinCriticalPoint t) := by
  filter_upwards [gamma0PrimitiveFourierAmplitude_factorization_critical_ae N a r Y hY n hn ρ hρ hcρ hsρ] with t ht
  rw [gamma0ABLEisensteinRho_scale]
  exact ht

def gamma0ABLContinuousRhoKernel (N : ℕ) [NeZero N] (r b : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) : ℂ :=
  ∑ j : Gamma0EisensteinCuspClasses N,
    gamma0ABLEisensteinRho N (gamma0EisensteinCuspClassRepresentative N j) r Y hY m hm (eisensteinCriticalPoint t)*
      star (gamma0ABLEisensteinRho N (gamma0EisensteinCuspClassRepresentative N j) b Y hY n hn (eisensteinCriticalPoint t))

theorem gamma0PrimitiveContinuousFourierKernel_sourceRho (N : ℕ) [NeZero N]
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) :
    gamma0PrimitiveContinuousFourierKernel N r b Y hY m n hm hn t =
      (4*Real.sqrt |(m : ℝ)| *Real.sqrt |(n : ℝ)| : ℂ)*
        gamma0ABLContinuousRhoKernel N r b Y hY m n hm hn t := by
  unfold gamma0PrimitiveContinuousFourierKernel gamma0ABLContinuousRhoKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← gamma0ABLEisensteinRho_scale N (gamma0EisensteinCuspClassRepresentative N j) r Y hY m hm,
    ← gamma0ABLEisensteinRho_scale N (gamma0EisensteinCuspClassRepresentative N j) b Y hY n hn,
    star_mul]
  norm_num
  ring

end ArtinMatthews
