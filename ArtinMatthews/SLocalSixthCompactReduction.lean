module

public import ArtinMatthews.SLocalCompactAnnuli
public import ArtinMatthews.SUnitSixthLogReduction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The norm-one S-local group has a fixed compact covering set modulo
sixth powers of the diagonal actual S-unit group. The covering is
derived from the complete S-unit logarithmic lattice. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SUnitGroup
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sixthLogBound (S : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  max 0 ((isBounded_iff_forall_norm_le).mp
    (sixthLogCompactSet_isCompact K S).isBounded).choose

theorem sixthLogCompactSet_norm_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    {z : LogHyperplane (K := K) S} (hz : z ∈ sixthLogCompactSet K S) :
    ‖z‖ ≤ sixthLogBound K S :=
  (((isBounded_iff_forall_norm_le).mp
    (sixthLogCompactSet_isCompact K S).isBounded).choose_spec z hz).trans (le_max_right _ _)

def sixthBalancedCompactSet (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (SWholeUnits K S) :=
  sLocalNormOneCompact K S (sixthLogBound K S)

theorem sixthBalancedCompactSet_isCompact (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsCompact (sixthBalancedCompactSet K S) := sLocalNormOneCompact_isCompact K S _

theorem sixthBalancedCompactSet_norm (S : Finset (HeightOneSpectrum (𝓞 K)))
    {y : SWholeUnits K S} (hy : y ∈ sixthBalancedCompactSet K S) : sLocalNorm K S y = 1 :=
  sLocalNormOneCompact_norm K S _ hy

private theorem norm_mem_annulus_of_log_bound (F : Type*) [NormedField F]
    (a : Fˣ) (B : ℝ) (h : |Real.log ‖(a : F)‖| ≤ B) :
    Real.exp (-B) ≤ ‖(a : F)‖ ∧ ‖(a : F)‖ ≤ Real.exp B := by
  have ha : 0 < ‖(a : F)‖ := norm_pos_iff.mpr a.ne_zero
  exact ⟨(Real.le_log_iff_exp_le ha).mp (abs_le.mp h).1,
    (Real.log_le_iff_le_exp ha).mp (abs_le.mp h).2⟩

theorem sLocalLog_bound_mem_annulus (S : Finset (HeightOneSpectrum (𝓞 K)))
    (y : SWholeUnits K S) (B : ℝ)
    (h : ‖sLocalLog K S (Additive.ofMul y)‖ ≤ B) : y ∈ sLocalAnnulus K S B := by
  constructor
  · intro w _
    apply norm_mem_annulus_of_log_bound
    have hw := (norm_le_pi_norm (sLocalLog K S (Additive.ofMul y)) (Sum.inl w)).trans h
    change |(w.mult : ℝ) * Real.log ‖(y.1 w : w.Completion)‖| ≤ B at hw
    rw [abs_mul, abs_of_pos (by exact_mod_cast (InfinitePlace.mult_pos (w := w)))] at hw
    have hweight := mul_le_mul_of_nonneg_right
      (InfinitePlace.one_le_mult (w := w))
      (abs_nonneg (Real.log ‖(y.1 w : w.Completion)‖))
    have hweight' : |Real.log ‖(y.1 w : w.Completion)‖| ≤
        (w.mult : ℝ) * |Real.log ‖(y.1 w : w.Completion)‖| := by
      simpa only [one_mul] using hweight
    exact hweight'.trans hw
  · intro v _
    apply norm_mem_annulus_of_log_bound
    exact (norm_le_pi_norm (sLocalLog K S (Additive.ofMul y)) (Sum.inr v)).trans h

theorem exists_sUnit_sixth_compact_reduction (S : Finset (HeightOneSpectrum (𝓞 K)))
    (y : SWholeUnits K S) (hy : sLocalNorm K S y = 1) :
    ∃ u : SUnitGroup (K := K) S,
      y * sWholeDiagonal K S ((u : Kˣ) ^ 6) ∈ sixthBalancedCompactSet K S := by
  let z : LogHyperplane (K := K) S :=
    ⟨sLocalLog K S (Additive.ofMul y), (sLocalNorm_eq_one_iff K S y).mp hy⟩
  obtain ⟨u, hu⟩ := exists_sUnit_sixth_log_reduction K S z
  have heq : sLocalLog K S
      (Additive.ofMul (y * sWholeDiagonal K S ((u : Kˣ) ^ 6))) =
      (z + fullLog (K := K) S (Additive.ofMul (u ^ 6)) : LogHyperplane (K := K) S) := by
    change sLocalLog K S
      (Additive.ofMul y + Additive.ofMul (sWholeDiagonal K S ((u : Kˣ) ^ 6))) = _
    rw [map_add]
    have hdiag := sLocalLog_diagonal K S (u ^ 6)
    exact congrArg (fun t => sLocalLog K S (Additive.ofMul y) + t) hdiag
  refine ⟨u, ?_, ?_⟩
  · apply sLocalLog_bound_mem_annulus
    rw [heq]
    exact sixthLogCompactSet_norm_le K S hu
  · exact (congrArg (coordinateSum (K := K) S) heq).trans
      (z + fullLog (K := K) S (Additive.ofMul (u ^ 6))).property

end
end ArtinMatthews
