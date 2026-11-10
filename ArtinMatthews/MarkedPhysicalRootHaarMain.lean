module

public import ArtinMatthews.MarkedPhysicalRootStripCount
public import ArtinMatthews.MarkedPhysicalRootTargetWindow
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The archimedean main term of the literal strip-root replacement.
The positive interval weights are integrated against the actual target
row.  The special-linear density is retained for the later line average. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalStripArcIndicator (z : ℤ × ℤ) (α β : ℝ) (r : ℝ) : ℝ :=
  if r ∈ Set.Icc α β ∧ |markedMinorIntegerTau r z| ≤ 16 then 1 else 0

theorem markedPhysicalStripArcIndicator_eq (z : ℤ × ℤ) (α β : ℝ) :
    markedPhysicalStripArcIndicator z α β =
      if markedPhysicalStripArcActive z α β then
        (Set.Icc (markedPhysicalStripArcLower z α) (markedPhysicalStripArcUpper z β)).indicator
          (fun _ => (1 : ℝ))
      else 0 := by
  funext r
  unfold markedPhysicalStripArcIndicator
  simp only [markedPhysicalTargetStrip_intersection]
  by_cases h : markedPhysicalStripArcActive z α β <;> simp [h, Set.indicator]

theorem markedPhysicalStripArcIndicator_integrable (z : ℤ × ℤ) (α β : ℝ) :
    Integrable (markedPhysicalStripArcIndicator z α β) volume := by
  rw [markedPhysicalStripArcIndicator_eq]
  split_ifs
  · exact (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (C := (1 : ℝ)) isCompact_Icc.measure_ne_top)
  · exact integrable_zero ℝ ℝ volume

theorem markedPhysicalStripArcIndicator_integral (z : ℤ × ℤ) (α β : ℝ) :
    (∫ r : ℝ, markedPhysicalStripArcIndicator z α β r) =
      if markedPhysicalStripArcActive z α β then
        markedPhysicalStripArcUpper z β-markedPhysicalStripArcLower z α
      else 0 := by
  rw [markedPhysicalStripArcIndicator_eq]
  split_ifs with h
  · rw [integral_indicator_const (1 : ℝ) measurableSet_Icc]
    simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr h.2),
      smul_eq_mul, mul_one]
  · simp only [Pi.zero_apply, integral_zero]

theorem markedPhysicalRootStripMain_integral (S : ℕ) (A B α β C D : ℝ) (z : ℤ × ℤ) :
    markedPhysicalRootStripMain S A B α β C D z =
      ((B-A)*(D-C)/((riemannZeta 2).re*
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
        ∫ r : ℝ, markedPhysicalStripArcIndicator z α β r := by
  rw [markedPhysicalStripArcIndicator_integral]
  unfold markedPhysicalRootStripMain
  split_ifs <;> ring

def markedPhysicalIntervalMajorant {ι : Type*} (I : Finset ι)
    (α β c : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ I, if r ∈ Set.Icc (α i) (β i) then c i else 0

theorem markedPhysicalIntervalMajorant_integrable {ι : Type*} (I : Finset ι)
    (α β c : ι → ℝ) : Integrable (markedPhysicalIntervalMajorant I α β c) volume := by
  unfold markedPhysicalIntervalMajorant
  apply integrable_finsetSum
  intro i _
  have hi : Integrable ((Set.Icc (α i) (β i)).indicator (fun _ => c i)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (C := c i) isCompact_Icc.measure_ne_top)
  convert hi using 1
  funext r
  by_cases hr : r ∈ Set.Icc (α i) (β i) <;> simp [Set.indicator, hr]

def markedPhysicalRootPositiveMain {ι : Type*} (I : Finset ι)
    (S : ℕ) (A B C D : ℝ) (α β c : ι → ℝ)
    (d b a : ℤ) (R Y Q : ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
    c iz.1 * ‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ *
      markedPhysicalRootStripMain S A B (α iz.1) (β iz.1) C D iz.2

theorem markedPhysicalRootPositiveMain_integral {ι : Type*} (I : Finset ι)
    (S : ℕ) (A B C D : ℝ) (α β c : ι → ℝ)
    (d b a : ℤ) (R Y Q : ℝ) (ψ : ℝ → ℂ) :
    markedPhysicalRootPositiveMain I S A B C D α β c d b a R Y Q ψ =
      ((B-A)*(D-C)/((riemannZeta 2).re*
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) *
      ∫ r : ℝ, ∑ iz ∈ I.product (markedPhysicalRootTargetWindow d R Y),
        c iz.1 * ‖markedBanEdgeKernel ψ Q Y b a (iz.2.2/d)‖ *
          markedPhysicalStripArcIndicator iz.2 (α iz.1) (β iz.1) r := by
  rw [integral_finsetSum _ (fun iz _ =>
    (markedPhysicalStripArcIndicator_integrable iz.2 (α iz.1) (β iz.1)).const_mul _)]
  simp only [integral_const_mul]
  unfold markedPhysicalRootPositiveMain
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro iz _
  rw [markedPhysicalRootStripMain_integral]
  ring

end ArtinMatthews
