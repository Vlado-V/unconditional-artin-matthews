module

public import ArtinMatthews.MarkedMinorArcRawEdgeSectors
public import ArtinMatthews.MarkedMinorArcRawEdgeJointDetector
public import ArtinMatthews.MarkedMinorArcRawEdgePatternTranspose
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact restricted-choice detector transpose for every literal sector,
including the pure-store/pure-promote pair and disjoint nonempty flags. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeDetectorSectorApply
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D : ℤ → ℤ → ℤ → ℂ)
    (k : MarkedRawEdgeSector) (f : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ c : {c : MarkedRawEdgeChoice hZ s //
      markedRawEdgeClassify (markedRawEdgeChoicePromoted c) c.store = k},
    (markedRawEdgeChoicePrimeMass ν V hZ s c.1 : ℂ) *
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ D s c.1 *
      f (markedRawEdgeTargetState hZ s c.1)

theorem markedRawEdgeDetectorSectorApply_eq_pattern
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D : ℤ → ℤ → ℤ → ℂ)
    (k : MarkedRawEdgeSector) (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeDetectorSectorApply ν V hZ η d₀ Y ρ χ D k f =
      markedRawEdgePatternApply ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (markedRawEdgeSectorKernel k (fun _ _ => markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D)) f := by
  classical
  funext s
  unfold markedRawEdgeDetectorSectorApply markedRawEdgePatternApply
  let good := fun c : MarkedRawEdgeChoice hZ s =>
    markedRawEdgeClassify (markedRawEdgeChoicePromoted c) c.store = k
  let F := fun c : MarkedRawEdgeChoice hZ s => (markedRawEdgeChoicePrimeMass ν V hZ s c : ℂ) *
    markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ D s c * f (markedRawEdgeTargetState hZ s c)
  have hsum : (∑ c : {c : MarkedRawEdgeChoice hZ s // good c}, F c.1) =
      ∑ c : MarkedRawEdgeChoice hZ s, if good c then F c else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter good) (by simp) F).symm
  rw [hsum]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [good,F]
  rw [markedRawEdgeChoiceCharge_original]
  by_cases hk : markedRawEdgeClassify (markedRawEdgeChoicePromoted c) c.store = k
  · simp only [hk, ite_true, markedRawEdgeSectorKernel]
    rw [markedRawEdgeChoiceDetectorCoefficient_eq_joint]
  · simp only [hk, ite_false, markedRawEdgeSectorKernel, mul_zero, zero_mul]

theorem markedRawEdgeDetectorSectorApply_sum
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D : ℤ → ℤ → ℤ → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeApplyDetector ν V hZ η d₀ Y ρ χ D f s =
      ∑ k : MarkedRawEdgeSector, markedRawEdgeDetectorSectorApply ν V hZ η d₀ Y ρ χ D k f s := by
  classical
  simp_rw [markedRawEdgeDetectorSectorApply_eq_pattern]
  rw [← markedRawEdgePatternApply_sector_sum]
  unfold markedRawEdgeApplyDetector markedRawEdgePatternApply
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoiceCharge_original, markedRawEdgeChoiceDetectorCoefficient_eq_joint]

theorem markedRawEdgeJointDetector_target_reverse
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D : ℤ → ℤ → ℤ → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D (markedRawEdgeTargetState hZ s c) s =
      markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeReverseDetector D)
        s (markedRawEdgeTargetState hZ s c) := by
  let copied := ((markedRawActiveSplit pads) s.2.1).1
  let a := ((markedRawActiveSplit pads) s.2.1).2
  let b := markedRawEdgeTargetLast s.2.2 c.promotions c.fresh
  have hs : (s.1,((markedRawActiveSplit pads).symm (copied,a),s.2.2)) = s := by
    change (s.1,((markedRawActiveSplit pads).symm ((markedRawActiveSplit pads) s.2.1),s.2.2)) = s
    rw [Equiv.symm_apply_apply]
  have hh := markedRawEdgeJointDetectorCoefficient_reverse hdisj hZ η d₀ Y ρ χ D
    copied c.target s.1 b a (markedRawEdgeTargetMemory hZ s c) s.2.2
  rw [hs] at hh
  exact hh

theorem markedRawEdgeDetectorSectorApply_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D : ℤ → ℤ → ℤ → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (k : MarkedRawEdgeSector) (f g : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (hg : ∀ z a, MarkedRawMemorySymmetric (fun m => g (z,(a,m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s *
      markedRawEdgeDetectorSectorApply ν V hZ η d₀ Y ρ χ D k f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s *
        markedRawEdgePatternApply ν (fun _ => 1) (fun j => ((V j)⁻¹ : ℝ)) hZ
          (markedRawEdgeSectorKernel (markedRawEdgeSectorSwap k)
            (fun _ _ target source => markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D source target)) g s := by
  rw [markedRawEdgeDetectorSectorApply_eq_pattern]
  have h := markedRawEdgePatternApply_transpose ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
    (markedRawEdgeSectorKernel k (fun _ _ => markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D))
    (by
      intro p q z a target m σ
      unfold markedRawEdgeSectorKernel
      split_ifs
      · exact markedRawEdgeJointDetectorCoefficient_source_permute hZ η d₀ Y ρ χ D hχ z a m σ target
      · rfl)
    (by
      intro p q source z a m σ
      unfold markedRawEdgeSectorKernel
      split_ifs
      · exact markedRawEdgeJointDetectorCoefficient_target_permute hZ η d₀ Y ρ χ D hχ source z a m σ
      · rfl) f g hf hg
  rw [markedRawEdgeSectorKernel_reverse] at h
  exact h

end
end ArtinMatthews
