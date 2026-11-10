module

public import ArtinMatthews.SpectralBareModulusSeries
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralJRegularizedWeight
public import ArtinMatthews.SpectralJRegularizedIntegrability
public import ArtinMatthews.SpectralMixedJRegularizedBound
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

/-! Removing the real Gaussian parameter from the literal mixed J modulus
sum using its proved, uniform summable majorant. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff Topology

namespace ArtinMatthews

theorem gamma0MixedJRegularizedBareFibre_uniform_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (m n : ℤ) (hmn : 0 < m*n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℝ, 0 ≤ L → ∀ q : Ioi (0 : ℕ),
      ‖gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) 1 q n m
        (spectralJRegularizedWeight f L)‖ ≤ B/(q.val : ℝ)^(9/8 : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := gamma0MixedJRegularizedHeatFibre_uniform_bound f hf hc hp r s hcop m n hmn
  have hm : m ≠ 0 := by intro h; simp [h] at hmn
  have hn : n ≠ 0 := by intro h; simp [h] at hmn
  refine ⟨B,hB,?_⟩
  intro L hL q
  have ht := gamma0TrueWidthHeatFibre_tendsto_bare (r*s) (gamma0CuspOneOver s) 1 q n m hn hm
    (spectralJRegularizedWeight f L) (spectralJRegularizedWeight_spectral_integrable f hf hc hp L hL)
  exact le_of_tendsto ((continuous_norm.tendsto _).comp ht)
    ((eventually_ge_atTop (1 : ℝ)).mono fun R hR => hbound L R hL hR q)

theorem gamma0MixedJRegularizedHeatSeries_uniform_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (m n : ℤ) (hmn : 0 < m*n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ L R : ℝ, 0 ≤ L → 1 ≤ R →
      Summable (fun q : Ioi (0 : ℕ) =>
        ‖gamma0TrueWidthHeatFibre (r*s) (gamma0CuspOneOver s) 1 q n m (spectralJRegularizedWeight f L) R‖) ∧
      ‖∑' q : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre (r*s) (gamma0CuspOneOver s) 1 q n m
        (spectralJRegularizedWeight f L) R‖ ≤ M := by
  obtain ⟨B,hB,hbound⟩ := gamma0MixedJRegularizedHeatFibre_uniform_bound f hf hc hp r s hcop m n hmn
  let g : Ioi (0 : ℕ) → ℝ := fun q => B/(q.val : ℝ)^(9/8 : ℝ)
  have hpseries : Summable (fun q : ℕ => 1/(q : ℝ)^(9/8 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hs : Summable g := by
    simpa only [g,mul_one_div,Function.comp_def] using! (hpseries.mul_left B).subtype (Ioi (0 : ℕ))
  refine ⟨∑' q, g q,tsum_nonneg (fun q => by dsimp [g]; positivity),?_⟩
  intro L R hL hR
  have hn : Summable (fun q : Ioi (0 : ℕ) =>
      ‖gamma0TrueWidthHeatFibre (r*s) (gamma0CuspOneOver s) 1 q n m (spectralJRegularizedWeight f L) R‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hbound L R hL hR) hs
  exact ⟨hn,(norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (hbound L R hL hR) hs)⟩

theorem gamma0MixedJRegularizedHeatSeries_tendsto_bare (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (m n : ℤ) (hmn : 0 < m*n) (L : ℝ) (hL : 0 ≤ L) :
    Summable (fun q : Ioi (0 : ℕ) =>
      ‖gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) 1 q n m (spectralJRegularizedWeight f L)‖) ∧
      Tendsto (fun R : ℝ => ∑' q : Ioi (0 : ℕ),
        gamma0TrueWidthHeatFibre (r*s) (gamma0CuspOneOver s) 1 q n m (spectralJRegularizedWeight f L) R)
        atTop (𝓝 (∑' q : Ioi (0 : ℕ),
          gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) 1 q n m (spectralJRegularizedWeight f L))) := by
  obtain ⟨B,hB,hbound⟩ := gamma0MixedJRegularizedHeatFibre_uniform_bound f hf hc hp r s hcop m n hmn
  have hm : m ≠ 0 := by intro h; simp [h] at hmn
  have hn : n ≠ 0 := by intro h; simp [h] at hmn
  have hseries : Summable (fun q : ℕ => 1/(q : ℝ)^(9/8 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hs : Summable (fun q : Ioi (0 : ℕ) => B/(q.val : ℝ)^(9/8 : ℝ)) := by
    simpa only [mul_one_div,Function.comp_def] using! (hseries.mul_left B).subtype (Ioi (0 : ℕ))
  have hlim (q : Ioi (0 : ℕ)) := gamma0TrueWidthHeatFibre_tendsto_bare (r*s)
    (gamma0CuspOneOver s) 1 q n m hn hm (spectralJRegularizedWeight f L)
      (spectralJRegularizedWeight_spectral_integrable f hf hc hp L hL)
  have hev : ∀ᶠ R : ℝ in atTop, ∀ q : Ioi (0 : ℕ),
      ‖gamma0TrueWidthHeatFibre (r*s) (gamma0CuspOneOver s) 1 q n m
        (spectralJRegularizedWeight f L) R‖ ≤ B/(q.val : ℝ)^(9/8 : ℝ) :=
    (eventually_ge_atTop (1 : ℝ)).mono fun R hR => hbound L R hL hR
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hs,
    tendsto_tsum_of_dominated_convergence hs hlim hev⟩
  intro q
  exact le_of_tendsto ((continuous_norm.tendsto _).comp (hlim q)) (hev.mono fun R hR => hR q)

end ArtinMatthews
