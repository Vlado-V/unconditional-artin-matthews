module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicGram.Definitions
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import OAI.NumberTheory.CubicGram.IntegerBasis
public import OAI.NumberTheory.CubicGram.LatticeCounts


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-!
# Convergent norm series on the Eisenstein lattice

These elementary lattice bounds provide a quantitative tail for the
Möbius residue sum after square-divisor truncation.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment

lemma eisenstein_norm_eq_sq (a : Eisenstein) : norm a = ‖a‖^2 :=
  (Complex.sq_norm (a : ℂ)).symm

instance eisenstein_discreteTopology : DiscreteTopology Eisenstein := by
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have he : Metric.ball (0 : Eisenstein) 1 = {0} := by
    ext a
    simp only [Metric.mem_ball,dist_zero_right,Set.mem_singleton_iff]
    constructor
    · intro ha
      by_contra hn
      have h := one_le_norm hn
      rw [eisenstein_norm_eq_sq] at h
      nlinarith [_root_.norm_nonneg a]
    · rintro rfl
      simp
  rw [← he]
  exact Metric.isOpen_ball

/-- The norm is the squared complex absolute value, so the convergence
threshold for its negative powers is one. -/
theorem summable_eisenstein_norm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun a : Eisenstein => norm a^(-s)) := by
  let L : Submodule ℤ ℂ := eisensteinRing.toSubmodule
  have hdim : Module.finrank ℤ L = 2 := by
    calc
      _ = Module.finrank ℤ Eisenstein := (eisensteinRing.toSubmoduleEquiv).finrank_eq
      _ = Module.finrank ℤ (Fin 2 → ℤ) := coordinatesEquiv.finrank_eq.symm
      _ = 2 := by simp
  have hL : DiscreteTopology L := eisenstein_discreteTopology
  let := hL
  have h := ZLattice.summable_norm_rpow L (-2*s) (by rw [hdim]; push_cast; linarith)
  change Summable (fun a : Eisenstein => ‖a‖^(-2*s)) at h
  apply h.congr
  intro a
  rw [eisenstein_norm_eq_sq,← Real.rpow_natCast ‖a‖ 2,← Real.rpow_mul (_root_.norm_nonneg a)]
  congr 1
  ring

lemma norm_rpow_tail_pointwise {D s t : ℝ} (hD : 0 < D) (hst : s < t)
    {a : Eisenstein} (ha : D < norm a) :
    norm a^(-t) ≤ D^(s-t)*norm a^(-s) := by
  have hn : 0 < norm a := hD.trans ha
  calc
    _ = norm a^(s-t)*norm a^(-s) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hD ha.le (by linarith))
      (Real.rpow_nonneg hn.le _)

/-- A stronger convergent exponent gives a power tail without losing a
factor to the norm fibers. -/
theorem eisenstein_norm_rpow_tail {D s t : ℝ} (hD : 0 < D)
    (hs : 1 < s) (hst : s < t) :
    (∑' a : Eisenstein, if D < norm a then norm a^(-t) else 0) ≤
      D^(s-t)*(∑' a : Eisenstein, norm a^(-s)) := by
  have ht := summable_eisenstein_norm_rpow (hs.trans hst)
  have htail := ht.indicator (fun a => D < norm a)
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ htail ((summable_eisenstein_norm_rpow hs).mul_left _)
  intro a
  change (if D < norm a then norm a^(-t) else 0) ≤ D^(s-t)*norm a^(-s)
  by_cases ha : D < norm a
  · simpa only [ha,ite_true] using norm_rpow_tail_pointwise hD hst ha
  · simp only [ha,ite_false]
    exact mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (norm_nonneg a) _)

end CubicFirstMoment

end

end OAI
