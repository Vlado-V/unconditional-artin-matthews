module

public import ArtinMatthews.MarkedRawBoundary
public import ArtinMatthews.MarkedPhysicalMarking
public import ArtinMatthews.MarkedMemoryTiltBasic
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

/-! Exact source-boundary summation. Initial active nu atoms remain in
the raw source measure; neither the boundary vector nor the chronological
birth coefficient absorbs them. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z : Finset (ℤ × ℤ)}
  (nu : (j : J) → ↥(P j) → ℝ) (z₀ : Z)

def markedMemoryBoundarySource (a : MarkedRawActive P M) : MarkedRawState P M B Z :=
  (z₀,a,markedRawBoundaryEmptyMemory P B)

theorem markedMemoryBoundarySource_mass (a : MarkedRawActive P M) :
    markedRawStateMass nu (markedMemoryBoundarySource (B := B) z₀ a)=markedRawActiveMass nu a := by
  rw [markedMemoryBoundarySource,markedRawStateMass,markedRawBoundaryEmptyMemory_mass,mul_one]

theorem markedMemorySourceBoundary_sum (F : MarkedRawState P M B Z → ℂ) :
    (∑ s : MarkedRawState P M B Z,(markedRawStateMass nu s : ℂ)*
      star (markedRawBoundary z₀ s)*F s)=
      ∑ a : MarkedRawActive P M,(markedRawActiveMass nu a : ℂ)*F (markedMemoryBoundarySource z₀ a) := by
  have ht (z : Z) (a : MarkedRawActive P M) (m : MarkedRawMemory P B) :
      (markedRawStateMass nu (z,a,m) : ℂ)*star (markedRawBoundary z₀ (z,a,m))*F (z,a,m)=
        if z=z₀ then if m=markedRawBoundaryEmptyMemory P B then
          (markedRawActiveMass nu a : ℂ)*F (z₀,a,markedRawBoundaryEmptyMemory P B) else 0 else 0 := by
    by_cases hz : z=z₀ <;> by_cases hm : m=markedRawBoundaryEmptyMemory P B
    · subst z; subst m
      simp [markedRawBoundary,markedRawStateMass,markedRawBoundaryEmptyMemory_mass]
    · simp [markedRawBoundary,hz,hm]
    · simp [markedRawBoundary,hz,hm]
    · simp [markedRawBoundary,hz,hm]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type,ht]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

theorem markedMemoryBoundarySource_tilt_normalization (V : J → ℝ) (q : ℝ) (N : ℕ)
    (a : MarkedRawActive P M)
    (hb : ∀ j k,markedMemoryBaseline q N ((a j k).1:ℕ)≠0) :
    (∏ j,∏ k,markedMemoryBaseline q N ((a j k).1:ℕ))*
        markedRawStateMass (fun j p => markedMemoryPrimeAtom (V j) q N p.1)
          (markedMemoryBoundarySource (B := B) z₀ a) =
      markedPhysicalMass V M * ∏ j,∏ k,(1/(((a j k).1:ℝ)+1)) := by
  rw [markedMemoryBoundarySource_mass]
  exact markedMemoryBaseline_rawActiveMass P V q N M a hb

end
end ArtinMatthews
