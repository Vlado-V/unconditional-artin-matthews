module

public import ArtinMatthews.SpectralPrimitiveFourierAmplitude
public import ArtinMatthews.SpectralPrimitiveFourierCritical
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

/-! The actual continuous Poincare pairing is the finite-cusp arithmetic
Fourier kernel times the two genuine K transforms, with literal dt/(2*pi).
This rewrites only the retained continuous term. -/

noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff Topology

namespace ArtinMatthews

def gamma0PrimitiveContinuousFourierKernel (N : ℕ) [NeZero N] (r b : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) : ℂ :=
  ∑ j : Gamma0EisensteinCuspClasses N,
    gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N j) r
        Y hY m hm (eisensteinCriticalPoint t)*
      star (gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N j) b
        Y hY n hn (eisensteinCriticalPoint t))

theorem gamma0PrimitiveEisensteinProduct_fourier_ae (N : ℕ) [NeZero N]
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    gamma0PrimitiveEisensteinProduct N r b Y hY m n ρ η =ᵐ[volume]
      fun t => (gamma0PrimitiveKTransform N r Y m ρ (eisensteinCriticalPoint t)*
        star (gamma0PrimitiveKTransform N b Y n η (eisensteinCriticalPoint t))*
          gamma0PrimitiveContinuousFourierKernel N r b Y hY m n hm hn t)/((2*Real.pi : ℝ) : ℂ) := by
  have hr : ∀ᵐ t ∂(volume : Measure ℝ), ∀ j : Gamma0EisensteinCuspClasses N,
      gamma0PrimitiveEisensteinTransform N (gamma0EisensteinCuspClassRepresentative N j) r
          Y hY m (eisensteinCriticalPoint t) ρ =
        gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N j) r
          Y hY m hm (eisensteinCriticalPoint t)*gamma0PrimitiveKTransform N r Y m ρ (eisensteinCriticalPoint t) :=
    ae_all_iff.mpr (fun j => gamma0PrimitiveFourierAmplitude_factorization_critical_ae N
      (gamma0EisensteinCuspClassRepresentative N j) r Y hY m hm ρ hρ hcρ hsρ)
  have hb : ∀ᵐ t ∂(volume : Measure ℝ), ∀ j : Gamma0EisensteinCuspClasses N,
      gamma0PrimitiveEisensteinTransform N (gamma0EisensteinCuspClassRepresentative N j) b
          Y hY n (eisensteinCriticalPoint t) η =
        gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N j) b
          Y hY n hn (eisensteinCriticalPoint t)*gamma0PrimitiveKTransform N b Y n η (eisensteinCriticalPoint t) :=
    ae_all_iff.mpr (fun j => gamma0PrimitiveFourierAmplitude_factorization_critical_ae N
      (gamma0EisensteinCuspClassRepresentative N j) b Y hY n hn η hη hcη hsη)
  filter_upwards [hr,hb] with t hrt hbt
  unfold gamma0PrimitiveEisensteinProduct gamma0PrimitiveContinuousFourierKernel
  apply congrArg (fun z : ℂ => z/((2*Real.pi : ℝ) : ℂ))
  calc
    _ = ∑ j : Gamma0EisensteinCuspClasses N,
        (gamma0PrimitiveKTransform N r Y m ρ (eisensteinCriticalPoint t)*
          star (gamma0PrimitiveKTransform N b Y n η (eisensteinCriticalPoint t)))*
        (gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N j) r
            Y hY m hm (eisensteinCriticalPoint t)*
          star (gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N j) b
            Y hY n hn (eisensteinCriticalPoint t))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hrt j,hbt j,star_mul]
      ring
    _ = _ := by rw [Finset.mul_sum]

theorem gamma0PrimitiveContinuousFourier_integrable (N : ℕ) [NeZero N]
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    IntegrableOn (fun t => (gamma0PrimitiveKTransform N r Y m ρ (eisensteinCriticalPoint t)*
      star (gamma0PrimitiveKTransform N b Y n η (eisensteinCriticalPoint t))*
        gamma0PrimitiveContinuousFourierKernel N r b Y hY m n hm hn t)/((2*Real.pi : ℝ) : ℂ)) (Ioi 0) := by
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun _ hy => hY.trans (hsρ hy)
  have hpη : tsupport η ⊆ Ioi (0 : ℝ) := fun _ hy => hY.trans (hsη hy)
  apply (gamma0PrimitiveEisenstein_product_integrable N r b Y hY m n ρ η
    hρ hη hcρ hcη hpρ hpη hsρ hsη).congr
  exact ae_restrict_of_ae (gamma0PrimitiveEisensteinProduct_fourier_ae N r b Y hY m n hm hn
    ρ η hρ hη hcρ hcη hsρ hsη)

theorem gamma0PrimitiveEisensteinPair_fourier_integral (N : ℕ) [NeZero N]
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    gamma0StoneEisensteinPair N (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ
      (fun _ hy => hY.trans (hsρ hy)))
      (gamma0PrimitiveFourierPoincareSeed N b n η hη hcη (fun _ hy => hY.trans (hsη hy))) =
      ∫ t in Ioi 0,(gamma0PrimitiveKTransform N r Y m ρ (eisensteinCriticalPoint t)*
        star (gamma0PrimitiveKTransform N b Y n η (eisensteinCriticalPoint t))*
          gamma0PrimitiveContinuousFourierKernel N r b Y hY m n hm hn t)/((2*Real.pi : ℝ) : ℂ) := by
  rw [gamma0PrimitiveEisensteinPair_eq_integral N r b Y hY m n ρ η hρ hη hcρ hcη
    (fun _ hy => hY.trans (hsρ hy)) (fun _ hy => hY.trans (hsη hy)) hsρ hsη]
  exact integral_congr_ae (ae_restrict_of_ae (gamma0PrimitiveEisensteinProduct_fourier_ae N r b Y hY m n hm hn
    ρ η hρ hη hcρ hcη hsρ hsη))

end ArtinMatthews
