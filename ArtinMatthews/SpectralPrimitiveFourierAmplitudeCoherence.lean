module

public import ArtinMatthews.SpectralPrimitiveFourierAmplitude
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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

/-! The scalar meromorphic Fourier amplitude is independent, as a germ,
of the auxiliary cusp-height cutoff and its chosen nonzero compact probe. -/

noncomputable section
open Set Filter
open scoped MatrixGroups Topology

namespace ArtinMatthews

theorem gamma0PrimitiveFourierAmplitude_height_coherence (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z) (n : ℤ) (hn : n ≠ 0) (s : ℂ) :
    gamma0PrimitiveFourierAmplitude N a r Y hY n hn =ᶠ[𝓝[≠] s]
      gamma0PrimitiveFourierAmplitude N a r Z hZ n hn := by
  let D (z : ℂ) := gamma0PrimitiveFourierAmplitude N a r Y hY n hn z-
    gamma0PrimitiveFourierAmplitude N a r Z hZ n hn z
  have hm : MeromorphicOn D univ := fun z _ =>
    (gamma0PrimitiveFourierAmplitude_meromorphic N a r Y hY n hn z).sub
      (gamma0PrimitiveFourierAmplitude_meromorphic N a r Z hZ n hn z)
  have hz : ∀ᶠ z in 𝓝[≠] (2 : ℂ), D z = 0 := by
    filter_upwards [gamma0PrimitiveFourierAmplitude_initial_germ N a r Y hY n hn (2 : ℂ) (by norm_num),
      gamma0PrimitiveFourierAmplitude_initial_germ N a r Z hZ n hn (2 : ℂ) (by norm_num)] with z hy hz
    dsimp only [D]
    rw [hy,hz,sub_self]
  have horder := hm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ s) (meromorphicOrderAt_eq_top_iff.mpr hz)
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp horder] with z hz
  exact sub_eq_zero.mp hz

end ArtinMatthews
