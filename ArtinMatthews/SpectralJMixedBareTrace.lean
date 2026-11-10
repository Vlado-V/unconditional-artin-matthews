module

public import ArtinMatthews.SpectralABLOppositeModulus
public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralJClippedEnergyTest
public import ArtinMatthews.SpectralJOddSynthesis
public import ArtinMatthews.SpectralJMixedGeometric
public import ArtinMatthews.SpectralJMixedRegularizedTrace
public import ArtinMatthews.SpectralJNativeOrientation
public import ArtinMatthews.SpectralMixedJRegularizationTannery
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
open MeasureTheory Set Filter Complex
open scoped ContDiff MatrixGroups Topology ComplexConjugate
noncomputable section

theorem gamma0MixedJ_bare_trace_real
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n) :
    gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
      (gamma0CuspOneOver s) 1 Y hY n m hn hm =
      (1 / 4 : ℂ) * ∑' q : Ioi (0 : ℕ),
        gamma0TrueWidthBareFibre (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJForwardSpectralWeight f) := by
  have hSpectral := gamma0JSource_regularization_tendsto_swapped
    f hf hc hp hreal r s hcop Y hY m n hm hn
  have hGeometric := (gamma0MixedJRegularizedBareSeries_tendsto
    f hf hc hp r s hcop m n hmn).2.comp tendsto_natCast_atTop_atTop
  apply tendsto_nhds_unique hSpectral
  apply (tendsto_const_nhds.mul hGeometric).congr'
  exact Eventually.of_forall (fun k : ℕ =>
    (gamma0MixedJ_regularized_bare_trace_real f hf hc hp hreal r s hr hcop
      Y hY m n hm hn hmn (k : ℝ) (Nat.cast_nonneg k)).symm)

theorem gamma0MixedJ_modulus_trace_real
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n) :
    (∑' q : Ioi (0 : ℕ),
      gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f) =
      4 * gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        (gamma0CuspOneOver s) 1 Y hY n m hn hm +
      (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis f)) := by
  have htrace := gamma0MixedJ_bare_trace_real f hf hc hp hreal
    r s hr hcop Y hY m n hm hn hmn
  have hgeom := (gamma0MixedJ_geometric_reconstruction f hf hc hp r s hcop
    m n hm hn hmn).2.2
  rw [hgeom, htrace]
  ring

end
end ArtinMatthews
