module

public import ArtinMatthews.SpectralHolomorphicCuspSeed
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! The actual weight-k slash has unit modulus in the Petersson-weighted
physical norm. This keeps the slash phases in the cut packet. -/
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralHolomorphicSlash_norm_sq_weight (k : ℕ) (G : SL(2, ℝ))
    (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖spectralHolomorphicSlash k G F z‖^2*z.im^k = ‖F (G • z)‖^2*(G • z).im^k := by
  have hnorm (H : UpperHalfPlane → ℂ) (w : UpperHalfPlane) :
      ‖UpperHalfPlane.petersson (k : ℤ) H H w‖ = ‖H w‖^2*w.im^k := by
    simp only [UpperHalfPlane.petersson,norm_mul,Complex.norm_conj,zpow_natCast,norm_pow,
      Complex.norm_real,Real.norm_of_nonneg w.im_pos.le,pow_two]
  have h := congrArg (fun x : ℂ => ‖x‖) (spectralHolomorphicPetersson_slash k G F F z)
  simpa only [hnorm] using h

end ArtinMatthews
