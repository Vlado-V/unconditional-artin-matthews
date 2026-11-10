module

public import ArtinMatthews.SpectralPeterssonCutPacket
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Sharp-cut seeds and their actual countable Poincare sums are measurable. -/
noncomputable section
open Set Matrix MeasureTheory UpperHalfPlane
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

variable {ι : Type*}

theorem spectralPeterssonHeightCutSeed_measurable (n : ℕ+) (A : ℝ) :
    Measurable (spectralPeterssonHeightCutSeed n A) := by
  have hs : MeasurableSet {z : UpperHalfPlane | A < 4*Real.pi*(n : ℝ)*z.im} := by
    apply measurableSet_lt measurable_const
    fun_prop
  have hf : Continuous (spectralHolomorphicCuspSeed (n : ℕ)) := by
    unfold spectralHolomorphicCuspSeed
    fun_prop
  exact Measurable.ite hs hf.measurable measurable_const

theorem spectralHolomorphicSlash_measurable (k : ℕ) (G : SL(2, ℝ))
    {F : UpperHalfPlane → ℂ} (hF : Measurable F) :
    Measurable (spectralHolomorphicSlash k G F) := by
  have he : spectralHolomorphicSlash k G F = fun z : UpperHalfPlane =>
      F (G • z)/(((G 1 0 : ℝ) : ℂ)*(z : ℂ)+((G 1 1 : ℝ) : ℂ))^k :=
    funext (spectralHolomorphicSlash_apply k G F)
  rw [he]
  apply Measurable.div
  · exact hF.comp (by fun_prop)
  · fun_prop

theorem gamma0PeterssonCutRow_measurable (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (A : ℝ) (p : Gamma0PeterssonSignedRow N 1 a) :
    Measurable (gamma0PeterssonCutRow N a k n A p) := by
  have he : gamma0PeterssonCutRow N a k n A p =
      spectralHolomorphicSlash k (gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val)
        (spectralPeterssonHeightCutSeed n A) :=
    funext (gamma0PeterssonCutRow_eq_slash N a k n A p)
  rw [he]
  exact spectralHolomorphicSlash_measurable k _ (spectralPeterssonHeightCutSeed_measurable n A)

theorem gamma0PeterssonCutPacket_measurable (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) {A : ℝ} (hA : 0 < A) :
    Measurable (gamma0PeterssonCutPacket N a k t α n A) := by
  classical
  letI : Countable (Gamma0PeterssonSignedRow N 1 a) := by
    unfold Gamma0PeterssonSignedRow
    infer_instance
  have hp (p : Gamma0PeterssonSignedRow N 1 a) :
      Measurable (fun z => gamma0PeterssonCutPacketRow N a k t α n A p z) := by
    unfold gamma0PeterssonCutPacketRow
    apply Finset.measurable_sum
    intro j hj
    exact measurable_const.mul (gamma0PeterssonCutRow_measurable N a k (n j) A p)
  have he : gamma0PeterssonCutPacket N a k t α n A =
      fun z => (1/2 : ℂ)*∑' p : Gamma0PeterssonSignedRow N 1 a,
        gamma0PeterssonCutPacketRow N a k t α n A p z :=
    funext (gamma0PeterssonCutPacket_eq_rows N a k t α n hA)
  rw [he]
  exact measurable_const.mul (Measurable.tsum hp)

end ArtinMatthews
