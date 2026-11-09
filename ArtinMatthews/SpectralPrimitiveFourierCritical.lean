module

public import ArtinMatthews.SpectralPrimitiveFourierAmplitudeCoherence
public import ArtinMatthews.SpectralMeromorphicLineAE


set_option backward.privateInPublic true
@[expose] public section

/-! The scalar arithmetic amplitude gives the actual compact Eisenstein
Fourier transform almost everywhere on the critical line. The K order is
literally i*t and the auxiliary cutoff cancels from the amplitude. -/

noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff Topology

namespace ArtinMatthews

theorem gamma0PrimitiveKTransform_critical (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (n : ℤ) (ρ : ℝ → ℝ) (t : ℝ) :
    gamma0PrimitiveKTransform N r Y n ρ (eisensteinCriticalPoint t) =
      cuspBesselTransform ((t : ℂ)*Complex.I) (2*Real.pi*|(n : ℝ)|)
        (Y/(gamma0CuspTrueWidth N r : ℝ)) (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u)) := by
  have he : eisensteinCriticalPoint t-(1/2 : ℂ) = (t : ℂ)*Complex.I := by
    unfold eisensteinCriticalPoint
    push_cast
    ring
  unfold gamma0PrimitiveKTransform
  rw [he]

theorem gamma0PrimitiveFourierAmplitude_factorization_critical_ae (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hsρ : tsupport ρ ⊆ Ioi Y) :
    (fun t : ℝ => gamma0PrimitiveEisensteinTransform N a r Y hY n (eisensteinCriticalPoint t) ρ)
      =ᵐ[volume] fun t => gamma0PrimitiveFourierAmplitude N a r Y hY n hn (eisensteinCriticalPoint t)*
        gamma0PrimitiveKTransform N r Y n ρ (eisensteinCriticalPoint t) := by
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => hY.trans (hsρ hy)
  let D (s : ℂ) := gamma0PrimitiveEisensteinTransform N a r Y hY n s ρ-
    gamma0PrimitiveFourierAmplitude N a r Y hY n hn s*gamma0PrimitiveKTransform N r Y n ρ s
  have hD : Meromorphic D := fun s =>
    (gamma0PrimitiveEisensteinTransform_meromorphic N a r Y hY n ρ hρ hcρ hpρ hsρ s).sub
      ((gamma0PrimitiveFourierAmplitude_meromorphic N a r Y hY n hn s).mul
        (gamma0PrimitiveKTransform_analytic N r Y hY n hn ρ hρ hcρ hsρ s (mem_univ s)).meromorphicAt)
  have hz (s : ℂ) : ∀ᶠ z in 𝓝[≠] s,D z = 0 := by
    filter_upwards [gamma0PrimitiveFourierAmplitude_factorization_germ N a r Y hY n hn ρ hρ hcρ hsρ s] with z hz
    exact sub_eq_zero.mpr hz
  have h := spectralMeromorphic_zero_ae_of_zero_germs D hD hz
    eisensteinCriticalPoint eisensteinCriticalPoint_injective
  filter_upwards [h] with t ht
  exact sub_eq_zero.mp ht

theorem gamma0PrimitiveFourierAmplitude_height_critical_ae (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z) (n : ℤ) (hn : n ≠ 0) :
    (fun t : ℝ => gamma0PrimitiveFourierAmplitude N a r Y hY n hn (eisensteinCriticalPoint t))
      =ᵐ[volume] fun t => gamma0PrimitiveFourierAmplitude N a r Z hZ n hn (eisensteinCriticalPoint t) := by
  let D (s : ℂ) := gamma0PrimitiveFourierAmplitude N a r Y hY n hn s-
    gamma0PrimitiveFourierAmplitude N a r Z hZ n hn s
  have hD : Meromorphic D := fun s =>
    (gamma0PrimitiveFourierAmplitude_meromorphic N a r Y hY n hn s).sub
      (gamma0PrimitiveFourierAmplitude_meromorphic N a r Z hZ n hn s)
  have hz (s : ℂ) : ∀ᶠ z in 𝓝[≠] s,D z = 0 := by
    filter_upwards [gamma0PrimitiveFourierAmplitude_height_coherence N a r Y Z hY hZ n hn s] with z hz
    exact sub_eq_zero.mpr hz
  have h := spectralMeromorphic_zero_ae_of_zero_germs D hD hz
    eisensteinCriticalPoint eisensteinCriticalPoint_injective
  filter_upwards [h] with t ht
  exact sub_eq_zero.mp ht

end ArtinMatthews
