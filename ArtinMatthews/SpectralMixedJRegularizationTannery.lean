module

public import ArtinMatthews.SpectralBareModulusSeries
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralJRegularizedWeight
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralJRegularizedKernelLimit
public import ArtinMatthews.SpectralMixedJHeatTannery
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
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

/-! Removing the pole regularizer from the same-sign mixed J modulus sum.
The limiting series is the literal bare kernel of the forward transform. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff Topology

namespace ArtinMatthews

theorem gamma0MixedJRegularizedBareSeries_tendsto (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (m n : ℤ) (hmn : 0 < m*n) :
    Summable (fun q : Ioi (0 : ℕ) =>
      ‖gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) 1 q n m (spectralJForwardSpectralWeight f)‖) ∧
      Tendsto (fun L : ℝ => ∑' q : Ioi (0 : ℕ),
        gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) 1 q n m (spectralJRegularizedWeight f L))
        atTop (𝓝 (∑' q : Ioi (0 : ℕ),
          gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) 1 q n m (spectralJForwardSpectralWeight f))) := by
  obtain ⟨B,hB,hbound⟩ := gamma0MixedJRegularizedBareFibre_uniform_bound f hf hc hp r s hcop m n hmn
  have hm : m ≠ 0 := by intro h; simp [h] at hmn
  have hn : n ≠ 0 := by intro h; simp [h] at hmn
  have hseries : Summable (fun q : ℕ => 1/(q : ℝ)^(9/8 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hs : Summable (fun q : Ioi (0 : ℕ) => B/(q.val : ℝ)^(9/8 : ℝ)) := by
    simpa only [mul_one_div,Function.comp_def] using! (hseries.mul_left B).subtype (Ioi (0 : ℕ))
  have hlim (q : Ioi (0 : ℕ)) :
      Tendsto (fun L : ℝ => gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) 1 q n m
        (spectralJRegularizedWeight f L)) atTop
        (𝓝 (gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) 1 q n m (spectralJForwardSpectralWeight f))) := by
    have ha := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
    have hb := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
    have hC := gamma0TrueWidthModulus_pos (r*s) (gamma0CuspOneOver s) 1 (Nat.cast_pos.mpr q.property)
    have hX : 0 < Real.sqrt (|cuspFourierFrequency 1 n| * |cuspFourierFrequency 1 m|)*
        (2/gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) 1 (q.val : ℝ)) := by positivity
    exact tendsto_const_nhds.mul (spectralJRegularizedBareKernel_tendsto f hf hc hp n m hX)
  have hev : ∀ᶠ L : ℝ in atTop, ∀ q : Ioi (0 : ℕ),
      ‖gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) 1 q n m
        (spectralJRegularizedWeight f L)‖ ≤ B/(q.val : ℝ)^(9/8 : ℝ) :=
    (eventually_ge_atTop (0 : ℝ)).mono fun L hL => hbound L hL
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hs,
    tendsto_tsum_of_dominated_convergence hs hlim hev⟩
  intro q
  exact le_of_tendsto ((continuous_norm.tendsto _).comp (hlim q)) (hev.mono fun L hL => hL q)

end ArtinMatthews
