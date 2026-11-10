module

public import ArtinMatthews.CircleShiftedFrequency
public import ArtinMatthews.CircleShiftedParametrization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! Reindexing the actual equation-and-congruence fiber by the original
shifted variable, with exact finite support and no multiplicity factor. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def circleShiftedIndices (d m3 m4 K1 K2 : ℕ) : Finset ℕ :=
  (Finset.range (K1+1)).filter (fun n => d*m3*n+1≤K1 ∧ d*m4*n+1≤K2)

def circleShiftedPairs (d m3 m4 K1 K2 : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)).filter
    (fun k => circleShiftedFrequency m3 m4 k=0 ∧ (d : ℤ)∣((k.1 : ℤ)-1))

theorem circleShiftedPairs_image (d m3 m4 K1 K2 : ℕ) (hd : 0<d) (hm3 : 0 < m3)
    (h34 : m3.Coprime m4) (h3d : m3.Coprime d) :
    circleShiftedPairs d m3 m4 K1 K2 =
      (circleShiftedIndices d m3 m4 K1 K2).image (fun n => (d*m3*n+1,d*m4*n+1)) := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨hkbox,hkcond⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1,hk2⟩ := Finset.mem_product.mp hkbox
    obtain ⟨hk1lo,hk1hi⟩ := Finset.mem_Icc.mp hk1
    obtain ⟨hk2lo,hk2hi⟩ := Finset.mem_Icc.mp hk2
    obtain ⟨n,h1,h2⟩ := (circleShifted_parametrization d m3 m4 hm3 h34 h3d k hk1lo hk2lo).mp hkcond
    have hnle : n≤d*m3*n := by nlinarith [Nat.mul_pos hd hm3]
    apply Finset.mem_image.mpr
    refine ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,?_,?_⟩,?_⟩
    · omega
    · omega
    · omega
    · exact Prod.ext h1.symm h2.symm
  · rintro hk
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨_hn,h1,h2⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,h1⟩,
      Finset.mem_Icc.mpr ⟨by omega,h2⟩⟩,?_⟩
    exact (circleShifted_parametrization d m3 m4 hm3 h34 h3d _ (by omega) (by omega)).mpr
      ⟨n,rfl,rfl⟩

theorem circleShifted_sum (d m3 m4 K1 K2 : ℕ) (hd : 0<d) (hm3 : 0 < m3)
    (h34 : m3.Coprime m4) (h3d : m3.Coprime d) (a : ℕ×ℕ → ℂ) :
    (∑ k∈circleShiftedPairs d m3 m4 K1 K2, a k) =
      ∑ n∈circleShiftedIndices d m3 m4 K1 K2, a (d*m3*n+1,d*m4*n+1) := by
  rw [circleShiftedPairs_image d m3 m4 K1 K2 hd hm3 h34 h3d]
  apply Finset.sum_image
  intro n _hn t _ht h
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hd hm3)
  have hh := congrArg Prod.fst h
  dsimp at hh
  omega

end ArtinMatthews
