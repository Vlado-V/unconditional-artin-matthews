module

public import ArtinMatthews.SpectralDecayingPoincare
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
public import Mathlib.RingTheory.PiTensorProduct
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

/-! The compact seed approximants are literal height cutoffs of the
original Fourier seed, in the stated integral cusp chart. -/

noncomputable section
open Set Filter
open scoped MatrixGroups ContDiff Topology
namespace ArtinMatthews

def gamma0PrimitiveDecayingSeedValue (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (n : ℤ)
    (P : SpectralDecayingHeightProfile) (z : UpperHalfPlane) : ℂ :=
  gamma0PrimitiveFourierScale N a*
    ((spectralHorizontalPartition (N : ℝ) (a • z).re*P.value (a • z).im : ℝ) : ℂ)*
    star (cuspFourierPhase (N : ℝ) ((gamma0CuspFrequencyStep N a : ℤ)*n) (a • z).re)

theorem gamma0PrimitiveHeightBlockSeed_apply (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (P : SpectralDecayingHeightProfile)
    (A : ℝ) (hA : 0 < A) (z : UpperHalfPlane) :
    (gamma0PrimitiveHeightBlockSeed N a n P A hA).val z =
      (spectralHeightAnnularBlock A (a • z).im : ℂ)*gamma0PrimitiveDecayingSeedValue N a n P z := by
  change gamma0PrimitiveFourierScale N a •
    (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      ((gamma0CuspFrequencyStep N a : ℤ)*n) (spectralHeightProfileBlock A P.value)
      (spectralHeightProfileBlock_contDiff hA P.value P.smooth)
      (spectralHeightProfileBlock_compact hA P.value)
      (spectralHeightProfileBlock_positive hA P.value)).val (a • z) = _
  rw [cuspFourierTestSeed_apply,smul_eq_mul,gamma0PrimitiveDecayingSeedValue,spectralHeightProfileBlock]
  push_cast
  ring

theorem gamma0PrimitiveDecayingCutoffSeed_apply (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (P : SpectralDecayingHeightProfile)
    (K : ℕ) (z : UpperHalfPlane) :
    (gamma0PrimitiveDecayingCutoffSeed N a n P K).val z =
      (spectralHeightAnnularPartial K (a • z).im : ℂ)*gamma0PrimitiveDecayingSeedValue N a n P z := by
  simp only [gamma0PrimitiveDecayingCutoffSeed,Submodule.coe_sum,Submodule.coe_add,
    CompactlySupportedContinuousMap.sum_apply,CompactlySupportedContinuousMap.add_apply,
    gamma0PrimitiveHeightBlockSeed_apply,← add_mul,← Complex.ofReal_add]
  rw [← Finset.sum_mul,← Complex.ofReal_sum]
  rfl

theorem gamma0PrimitiveDecayingCutoffSeed_eventually (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (P : SpectralDecayingHeightProfile) (z : UpperHalfPlane) :
    ∀ᶠ K : ℕ in atTop,
      (gamma0PrimitiveDecayingCutoffSeed N a n P K).val z =
        gamma0PrimitiveDecayingSeedValue N a n P z := by
  filter_upwards [spectralHeightAnnularPartial_eventually_one (a • z).im_pos] with K hK
  rw [gamma0PrimitiveDecayingCutoffSeed_apply,hK,Complex.ofReal_one,one_mul]

end ArtinMatthews
