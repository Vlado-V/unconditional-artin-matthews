module

public import ArtinMatthews.SpectralCoreLocalization
public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralRellichHyperbolic
public import ArtinMatthews.SpectralPoincareLinear
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Actual fixed compact localizations of the arithmetic smooth energy core. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

/-- Literal multiplication by a compact smooth cutoff, in invariant-volume L². -/
def gamma0LocalizedSeedLp (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    Lp ℂ 2 (volume : Measure UpperHalfPlane) :=
  spectralHyperbolicRectangleLp ha hab
    (spectralCoreLocalization φ ha hφ (gamma0PoincareSeed N ψ.val)
      (gamma0SmoothSeed_representative_smooth N ψ))
    (spectralCoreLocalization_support φ ha hφ (gamma0PoincareSeed N ψ.val)
      (gamma0SmoothSeed_representative_smooth N ψ))

theorem gamma0LocalizedSeedLp_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0LocalizedSeedLp φ ha hab hφ N ψ =ᵐ[volume]
      (fun z : UpperHalfPlane => φ (z.re,z.im) * gamma0PoincareSeed N ψ.val z) := by
  filter_upwards [spectralHyperbolicRectangleLp_ae ha hab
    (spectralCoreLocalization φ ha hφ (gamma0PoincareSeed N ψ.val)
      (gamma0SmoothSeed_representative_smooth N ψ))
    (spectralCoreLocalization_support φ ha hφ (gamma0PoincareSeed N ψ.val)
      (gamma0SmoothSeed_representative_smooth N ψ))] with z hz
  change (gamma0LocalizedSeedLp φ ha hab hφ N ψ) z = _ at hz
  rw [hz, spectralCoreLocalization_apply]
  rw [show ((z.re : ℂ)+z.im*Complex.I) = (z : ℂ) from Complex.re_add_im _]
  rw [UpperHalfPlane.ofComplex_apply]

/-- This localization is linear in the actual compact seed. -/
def gamma0LocalizedSeedLinear (N : ℕ) [NeZero N] :
    h2SmoothCompactSeeds →ₗ[ℂ] Lp ℂ 2 (volume : Measure UpperHalfPlane) where
  toFun := gamma0LocalizedSeedLp φ ha hab hφ N
  map_add' ψ ξ := by
    apply Lp.ext
    filter_upwards [gamma0LocalizedSeedLp_ae φ ha hab hφ N (ψ+ξ),
      gamma0LocalizedSeedLp_ae φ ha hab hφ N ψ,
      gamma0LocalizedSeedLp_ae φ ha hab hφ N ξ,
      Lp.coeFn_add (gamma0LocalizedSeedLp φ ha hab hφ N ψ)
        (gamma0LocalizedSeedLp φ ha hab hφ N ξ)] with z hs hψ hξ hadd
    rw [hadd, hs]
    change _ = (gamma0LocalizedSeedLp φ ha hab hφ N ψ) z +
      (gamma0LocalizedSeedLp φ ha hab hφ N ξ) z
    rw [hψ,hξ]
    change φ (z.re,z.im) * arithmeticPoincareSeed _ (ψ.val+ξ.val) z = _
    rw [arithmeticPoincareSeed_add]
    exact mul_add _ _ _
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [gamma0LocalizedSeedLp_ae φ ha hab hφ N (c • ψ),
      gamma0LocalizedSeedLp_ae φ ha hab hφ N ψ,
      Lp.coeFn_smul c (gamma0LocalizedSeedLp φ ha hab hφ N ψ)] with z hs hψ hsmul
    simp only [RingHom.id_apply]
    rw [hsmul, hs]
    change _ = c • (gamma0LocalizedSeedLp φ ha hab hφ N ψ) z
    rw [hψ]
    change φ (z.re,z.im) * arithmeticPoincareSeed _ (c • ψ.val) z = _
    rw [arithmeticPoincareSeed_smul]
    change _ * (c * _) = c * (_ * _)
    dsimp only [gamma0PoincareSeed]
    ring

theorem gamma0LocalizedSeedLp_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0LocalizedSeedLp φ ha hab hφ N ψ‖^2 =
      ∫ z : UpperHalfPlane, ‖φ (z.re,z.im) * gamma0PoincareSeed N ψ.val z‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gamma0LocalizedSeedLp_ae φ ha hab hφ N ψ] with z hz
  rw [real_inner_self_eq_norm_sq, hz]

end ArtinMatthews
