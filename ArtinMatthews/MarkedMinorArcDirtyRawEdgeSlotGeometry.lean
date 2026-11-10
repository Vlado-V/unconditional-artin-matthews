module

public import ArtinMatthews.MarkedMinorArcRawSlotAverage
public import ArtinMatthews.MarkedMinorArcBanRawCollision
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

/-! Exact source product and ban invariance under the actual slot action. -/
namespace ArtinMatthews

open scoped BigOperators

theorem markedDirtyRawStateSlot_full_product {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) :
    markedSourceFullProduct (markedRawNumericActive (markedRawSlotEquiv σ s).2.1)=
      markedSourceFullProduct (markedRawNumericActive s.2.1) := by
  change (∏ j, ∏ k, ((s.2.1 j (σ j k)).1:ℕ))=∏ j, ∏ k, ((s.2.1 j k).1:ℕ)
  apply Finset.prod_congr rfl
  intro j _
  exact Equiv.prod_comp (σ j) (fun k => ((s.2.1 j k).1:ℕ))

theorem markedDirtyRawStateSlot_crossBan_iff {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) (target : (j : J) → ↥(P j)) :
    MarkedRawFullCrossBan (markedRawSlotEquiv σ s).2.1 target ↔ MarkedRawFullCrossBan s.2.1 target := by
  constructor
  · rintro ⟨i,j,k,hk⟩
    exact ⟨i,j,σ j k,hk⟩
  · rintro ⟨i,j,k,hk⟩
    refine ⟨i,j,(σ j).symm k,?_⟩
    change (target i).1=(s.2.1 j (σ j ((σ j).symm k))).1
    simpa only [Equiv.apply_symm_apply] using hk

theorem markedDirtyRawStateSlot_distinct_iff {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) :
    (∀ j, Function.Injective ((markedRawSlotEquiv σ s).2.1 j)) ↔ (∀ j, Function.Injective (s.2.1 j)) := by
  constructor
  · intro h j k l hkl
    have he : (markedRawSlotEquiv σ s).2.1 j ((σ j).symm k)=
        (markedRawSlotEquiv σ s).2.1 j ((σ j).symm l) := by
      change s.2.1 j (σ j ((σ j).symm k))=s.2.1 j (σ j ((σ j).symm l))
      simpa only [Equiv.apply_symm_apply] using hkl
    exact (σ j).symm.injective (h j he)
  · intro h j
    exact (h j).comp (σ j).injective

end ArtinMatthews
