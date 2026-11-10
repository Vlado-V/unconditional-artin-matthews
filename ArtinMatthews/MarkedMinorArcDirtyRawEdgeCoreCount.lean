module

public import ArtinMatthews.MarkedMinorArcDirtyGoodRow
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite coding of the source-omission/old-index/target row into
the literal counted dirty choices. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev MarkedDirtyRawCountedChoice {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) :=
  Σ k : ↥(markedRawDirtyDistinguishedIndices source memory jstar),
    Σ c : ↥(markedRawDirtyTargetChoices source (memory.2 jstar k.1)
      (markedRawPromotionProductSupport memory I) V hV z T Q),
      {t : MarkedRawPromotionTuple memory I // markedRawPromotionTuplePrimeProduct memory I t=c.1.1.2}

instance markedDirtyRawCountedChoice_fintype {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) :
    Fintype (MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q) := by
  classical
  unfold MarkedDirtyRawCountedChoice
  infer_instance

def markedDirtyRawCountedWeight {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (ρ : ℝ)
    (c : MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q) : ℝ :=
  markedUniformOmissionWeight M c.2.1.1.1.1 *
    markedRawPromotionTupleDamping memory I c.2.1.1.2.1 (hV _ c.2.1.1.2.2) ρ (fun _ => 0) c.2.2.1

theorem markedDirtyRawCountedWeight_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (ρ : ℝ) :
    (∑ c : MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q,
      markedDirtyRawCountedWeight source memory jstar I V hV z T Q ρ c) =
      markedRawDirtyGoodChoiceMass source memory jstar I V hV z T Q ρ (fun _ _ _ => 0) := by
  classical
  rw [Fintype.sum_sigma]
  unfold markedRawDirtyGoodChoiceMass
  rw [← Finset.sum_coe_sort (markedRawDirtyDistinguishedIndices source memory jstar)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fintype.sum_sigma]
  rw [← Finset.sum_coe_sort (markedRawDirtyTargetChoices source (memory.2 jstar k.1)
    (markedRawPromotionProductSupport memory I) V hV z T Q)]
  apply Finset.sum_congr rfl
  intro c _
  unfold markedDirtyRawCountedWeight
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.sum_subtype (Finset.univ.filter (fun t : MarkedRawPromotionTuple memory I =>
    markedRawPromotionTuplePrimeProduct memory I t=c.1.1.2)) (by simp)
    (fun t => markedRawPromotionTupleDamping memory I c.1.2.1 (hV _ c.1.2.2) ρ (fun _ => 0) t)).symm

end ArtinMatthews
