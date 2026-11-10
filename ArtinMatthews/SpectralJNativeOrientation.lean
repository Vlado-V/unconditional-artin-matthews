module

public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralJClippedEnergyTest
public import ArtinMatthews.SpectralJRegularizedEnergyTest
public import ArtinMatthews.SpectralJClippedReality
public import ArtinMatthews.SpectralJNativeLimit
public import ArtinMatthews.SpectralJRegularizedReality
public import ArtinMatthews.SpectralNativeHermitian
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

namespace ArtinMatthews
open Set Filter
open scoped ContDiff MatrixGroups Topology ComplexConjugate
noncomputable section

theorem gamma0JSource_regularization_tendsto_swapped (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x)
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Tendsto (fun k : ℕ => gamma0BareSourceSpectralSide (r * s)
      (spectralJRegularizedEnergyTest f hf hc hp (k : ℝ) (Nat.cast_nonneg k))
        (gamma0CuspOneOver s) 1 Y hY n m hn hm) atTop
      (𝓝 (gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        (gamma0CuspOneOver s) 1 Y hY n m hn hm)) := by
  have h := continuous_star.continuousAt.tendsto.comp
    (gamma0JSource_regularization_tendsto f hf hc hp r s hcop Y hY m n hm hn)
  have hfun : (fun k : ℕ => star (gamma0BareSourceSpectralSide (r * s)
      (spectralJRegularizedEnergyTest f hf hc hp (k : ℝ) (Nat.cast_nonneg k))
        1 (gamma0CuspOneOver s) Y hY m n hm hn)) =
      (fun k : ℕ => gamma0BareSourceSpectralSide (r * s)
        (spectralJRegularizedEnergyTest f hf hc hp (k : ℝ) (Nat.cast_nonneg k))
          (gamma0CuspOneOver s) 1 Y hY n m hn hm) := by
    funext k
    exact (gamma0BareSourceSpectralSide_real_swap (r * s) _
      (spectralJRegularizedEnergyTest_real f hf hc hp hReal _ (Nat.cast_nonneg k))
      (gamma0CuspOneOver s) 1 Y hY n m hn hm).symm
  have htarget :
      star (gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        1 (gamma0CuspOneOver s) Y hY m n hm hn) =
      gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        (gamma0CuspOneOver s) 1 Y hY n m hn hm :=
    (gamma0BareSourceSpectralSide_real_swap (r * s) _
      (spectralJClippedEnergyTest_real f hf hc hp hReal)
      (gamma0CuspOneOver s) 1 Y hY n m hn hm).symm
  simpa only [Function.comp_def, hfun, htarget] using h

end
end ArtinMatthews
