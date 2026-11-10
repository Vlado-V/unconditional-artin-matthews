module

public import ArtinMatthews.SpectralPrimitiveFourierAmplitude
public import ArtinMatthews.SpectralMeromorphicLineAE
public import ArtinMatthews.SpectralPrimitiveEisensteinBessel
public import ArtinMatthews.SpectralPrimitiveFourierAmplitudeCoherence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
