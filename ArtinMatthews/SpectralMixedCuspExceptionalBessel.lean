module

public import ArtinMatthews.SpectralCuspExceptionalMoment
public import ArtinMatthews.SpectralMixedSameCuspDiagonalGramBound
public import ArtinMatthews.SpectralKExceptionalPhysicalTest
public import ArtinMatthews.SpectralMixedCuspPhysicalBessel
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

/-! The finite exceptional-series singleton at the actual source cusp 1/s. -/

noncomputable section
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0MixedCusp_exceptional_singleton_compact_bound (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (u : Finset (Gamma0AllHeightSpectralIndex (r*s)))
    (n : ℤ) (hn : n ≠ 0) {A Y : ℝ} (hA : 0 < A) (hA₁ : 2*A ≤ 1) (hY : 0 < Y)
    (hYA : Y < A/(|cuspFourierFrequency 1 n|/
      (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)))
    (heig : ∀ i ∈ u, gamma0AllHeightGradientSpectralValue (r*s) i ≤ 1/4) :
    (Real.exp (-Real.exp 1)/16)^2*gamma0CuspExceptionalMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn A ≤
      1+8*spectralKloostermanDiagSum (r*s) n (|cuspFourierFrequency 1 n|/A) := by
  obtain ⟨F,hF,hcF,hSF,h01,hOne⟩ := spectralKExceptionalPhysicalTest_exists hA
  exact (gamma0CuspExceptionalMoment_le_physical (r*s) u (gamma0CuspOneOver s) Y hY n hn F
    hF.continuous hA hA₁ hSF (fun x => (h01 x).1) hOne heig).trans
      (gamma0MixedSameCusp_comparable_physical_finite_bessel r s hcop u n hn F hF hcF hA hY hYA hSF h01)

end ArtinMatthews
