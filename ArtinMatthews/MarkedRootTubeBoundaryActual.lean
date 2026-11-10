module

public import ArtinMatthews.MarkedRootTubeBoundary
public import ArtinMatthews.MarkedRootBoundaryScalar
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The genuine original root-parameter boundary is small before and
after integration. The factor fifteen is the exact normalized measure
mass, retained explicitly for the final physical moment estimate. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (hinj : Function.Injective e)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ u,‖η u‖≤1)
  (q ρ G H A W : ℝ) (hq₀ : 0≤q) (hq₁ : q≤1)
  (hρ : 0<ρ) (hρ₁ : ρ<1) (hgap : Real.sqrt q<ρ^2)
  (hG : 0<G) (hH : 1≤H) (hA : 0≤A) (hW : 0≤W)
  (hdepth : 100*(5*G+36)<(Fintype.card J:ℝ))
  (hψ : ∀ u,‖ψ u‖≤W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A)

include he hinj hη hηnorm hq₀ hq₁ hρ hρ₁ hgap hG hH hA hW hdepth hψ hsupp

theorem markedRootTubeBoundary_actual_bound :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0<d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ))≤Y →
      Y≤Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      ∀ (R : ℕ) (hR : 1≤R) (U V : ℝ) (p : ℝ × (ℝ × ℝ))
        (_hp : p∈markedRootBoxDomain) (orientation : ℕ → Bool),
      ‖markedRootTubeBoundary e x ψ η d₀ Y ((Real.log x)^(G+9)) q ρ
        R hR U V p orientation‖≤((Real.log x)^(-G))^(markedMemoryMomentLength x) := by
  filter_upwards [markedRootWindowGoodBoundary_actual_bound e he hinj ψ η hη hηnorm
    q ρ G H A W hq₀ hq₁ hρ hρ₁ hgap hG hH hA hW hdepth hψ hsupp] with x hx
  intro d₀ Y hd₀ hYlo hYhi R hR U V p hp orientation
  rw [markedRootTubeBoundary_eq_window e x ψ η d₀ Y ((Real.log x)^(G+9)) q ρ R hR U V p hp orientation]
  exact hx d₀ Y hd₀ hYlo hYhi R hR U V p hp orientation

theorem markedRootTubeBoundary_integral_actual_bound :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0<d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ))≤Y →
      Y≤Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      ∀ (R : ℕ) (hR : 1≤R) (U V : ℝ) (orientation : ℕ → Bool),
      ‖∫ p,markedRootTubeBoundary e x ψ η d₀ Y ((Real.log x)^(G+9)) q ρ
        R hR U V p orientation ∂markedNormalizedRootMeasure‖≤
        15*((Real.log x)^(-G))^(markedMemoryMomentLength x) := by
  filter_upwards [markedRootTubeBoundary_actual_bound e he hinj ψ η hη hηnorm
    q ρ G H A W hq₀ hq₁ hρ hρ₁ hgap hG hH hA hW hdepth hψ hsupp] with x hx
  intro d₀ Y hd₀ hYlo hYhi R hR U V orientation
  exact markedNormalizedRoot_integral_norm_le _ _
    (fun p hp => hx d₀ Y hd₀ hYlo hYhi R hR U V p hp orientation)

end ArtinMatthews
