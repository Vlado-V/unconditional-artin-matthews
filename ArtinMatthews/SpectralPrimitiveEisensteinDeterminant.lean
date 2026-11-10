module

public import ArtinMatthews.SpectralPrimitiveKTransform
public import ArtinMatthews.SpectralMeromorphicHalfPlaneIdentity
public import ArtinMatthews.SpectralPrimitiveEisensteinBessel
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

/-! The genuine compact Eisenstein tests have the same scalar arithmetic
factor. The initial K-Bessel formula propagates this identity as an actual
meromorphic germ at every parameter. -/

noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff Topology

namespace ArtinMatthews

theorem gamma0PrimitiveEisenstein_K_determinant_germ (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s,
      gamma0PrimitiveEisensteinTransform N a r Y hY n z ρ*gamma0PrimitiveKTransform N r Y n η z =
        gamma0PrimitiveEisensteinTransform N a r Y hY n z η*gamma0PrimitiveKTransform N r Y n ρ z := by
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => hY.trans (hsρ hy)
  have hpη : tsupport η ⊆ Ioi (0 : ℝ) := fun y hy => hY.trans (hsη hy)
  let Tρ (z : ℂ) := gamma0PrimitiveEisensteinTransform N a r Y hY n z ρ
  let Tη (z : ℂ) := gamma0PrimitiveEisensteinTransform N a r Y hY n z η
  let Kρ := gamma0PrimitiveKTransform N r Y n ρ
  let Kη := gamma0PrimitiveKTransform N r Y n η
  have hTρ : Meromorphic Tρ := gamma0PrimitiveEisensteinTransform_meromorphic N a r Y hY n ρ hρ hcρ hpρ hsρ
  have hTη : Meromorphic Tη := gamma0PrimitiveEisensteinTransform_meromorphic N a r Y hY n η hη hcη hpη hsη
  have hKρ : Meromorphic Kρ := fun z =>
    (gamma0PrimitiveKTransform_analytic N r Y hY n hn ρ hρ hcρ hsρ z (mem_univ z)).meromorphicAt
  have hKη : Meromorphic Kη := fun z =>
    (gamma0PrimitiveKTransform_analytic N r Y hY n hn η hη hcη hsη z (mem_univ z)).meromorphicAt
  let D (z : ℂ) := Tρ z*Kη z-Tη z*Kρ z
  have hD : Meromorphic D := fun z => ((hTρ z).mul (hKη z)).sub ((hTη z).mul (hKρ z))
  have hzero (z : ℂ) (hz : 1 < z.re) : D z = 0 := by
    dsimp only [D,Tρ,Tη,Kρ,Kη]
    rw [gamma0PrimitiveEisensteinTransform_initial_factor N a r Y hY n hn z hz ρ hρ hcρ hpρ hsρ,
      gamma0PrimitiveEisensteinTransform_initial_factor N a r Y hY n hn z hz η hη hcη hpη hsη]
    ring
  have h := spectralMeromorphic_zero_germ_of_initial_halfPlane D hD hzero s
  filter_upwards [h] with z hz
  exact sub_eq_zero.mp hz

end ArtinMatthews
