module

public import ArtinMatthews.MarkedMinorArcRawEdgeAction
public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryCoefficients
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
public import Mathlib.Tactic.ENatToNat
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

/-! Extracting the cost of a prescribed fresh prime. The remaining law is
not renormalized by a probability: the extracted scale is the given atom
upper bound. A prime outside its actual band gives zero mass. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPrescribedPrimeLaw {J : Type*} [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (Δ : ℝ) (S : Finset J) (ξ : J → Nat.Primes) (j : J) (p : ↥(P j)) : ℝ :=
  if j ∈ S then if p.1 = ξ j then ν j p/Δ else 0 else ν j p

theorem markedPrescribedPrimeLaw_nonneg {J : Type*} [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (S : Finset J) (ξ : J → Nat.Primes) :
    ∀ j p, 0 ≤ markedPrescribedPrimeLaw ν Δ S ξ j p := by
  intro j p
  unfold markedPrescribedPrimeLaw
  split_ifs
  · exact div_nonneg (hν j p) hΔ
  · exact le_rfl
  · exact hν j p

theorem markedPrescribedPrimeLaw_sum_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {Δ N : ℝ} (hΔ : 0 < Δ) (hN : 1 ≤ N)
    (hatom : ∀ j p, ν j p ≤ Δ) (hmass : ∀ j, (∑ p, ν j p) ≤ N)
    (S : Finset J) (ξ : J → Nat.Primes) :
    ∀ j, (∑ p, markedPrescribedPrimeLaw ν Δ S ξ j p) ≤ N := by
  classical
  intro j
  by_cases hj : j ∈ S
  · by_cases hp : ξ j ∈ P j
    · let p₀ : ↥(P j) := ⟨ξ j,hp⟩
      have hsum : (∑ p, markedPrescribedPrimeLaw ν Δ S ξ j p) = ν j p₀/Δ := by
        calc
          _ = markedPrescribedPrimeLaw ν Δ S ξ j p₀ := by
            apply Finset.sum_eq_single p₀
            · intro p _ hne
              have hval : p.1 ≠ ξ j := fun h => hne (Subtype.ext h)
              simp only [markedPrescribedPrimeLaw,hj,hval,ite_true,ite_false]
            · simp
          _ = _ := by simp only [markedPrescribedPrimeLaw,hj,p₀,ite_true]
      rw [hsum]
      exact ((div_le_one hΔ).mpr (hatom j p₀)).trans hN
    · have hsum : (∑ p, markedPrescribedPrimeLaw ν Δ S ξ j p) = 0 := by
        apply Finset.sum_eq_zero
        intro p _
        have hval : p.1 ≠ ξ j := fun h => hp (h ▸ p.2)
        simp only [markedPrescribedPrimeLaw,hj,hval,ite_true,ite_false]
      rw [hsum]
      exact zero_le_one.trans hN
  · simpa only [markedPrescribedPrimeLaw,hj,ite_false] using hmass j

def MarkedRawEdgePrescribedFresh {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (S : Finset J) (ξ : J → Nat.Primes) (c : MarkedRawEdgeChoice hZ s) : Prop :=
  ∀ j ∈ S, c.promotions j = none ∧
    (markedRawEdgeTargetLast s.2.2 c.promotions c.fresh j).1 = ξ j

theorem markedRawEdgePrescribedFresh_mass {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {Δ : ℝ} (hΔ : Δ ≠ 0) {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (S : Finset J) (ξ : J → Nat.Primes) (c : MarkedRawEdgeChoice hZ s)
    (hc : MarkedRawEdgePrescribedFresh hZ s S ξ c) :
    markedRawEdgeChoicePrimeMass ν V hZ s c =
      Δ^S.card * markedRawEdgeChoicePrimeMass (markedPrescribedPrimeLaw ν Δ S ξ) V hZ s c := by
  classical
  have hprod : (∏ j : J, if j ∈ S then Δ else 1) = Δ^S.card := by
    simp
  rw [markedRawEdgeChoicePrimeMass_eq_targetLast,
    markedRawEdgeChoicePrimeMass_eq_targetLast,← hprod,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ S
  · obtain ⟨hf,hp⟩ := hc j hj
    simp only [hf,Option.isSome_none,Bool.false_eq_true,ite_false,
      markedPrescribedPrimeLaw,hj,hp,ite_true]
    field_simp
  · simp only [hj,ite_false,markedPrescribedPrimeLaw,one_mul]

end ArtinMatthews
