module

public import ArtinMatthews.MarkedMemoryIndependentLineExpectation
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact marginalization of a finite uniform line tuple. Unselected
coordinates are averaged out; an arbitrary observable of all selected
coordinates, including coupled repeated visits, remains unchanged. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedFiniteSubsetPiRestrict {α : Type*} [DecidableEq α]
    {s t : Finset α} (hst : s ⊆ t) (F : α → Type*)
    (ell : (p : t) → F p.1) : (p : s) → F p.1 :=
  fun p => ell ⟨p.1,hst p.2⟩

def markedFiniteSubsetPiEquiv {α : Type*} [DecidableEq α]
    (s t : Finset α) (hst : s ⊆ t) (F : α → Type*) :
    ((p : t) → F p.1) ≃ ((p : s) → F p.1) × ((p : ↥(t \ s)) → F p.1) where
  toFun ell := (markedFiniteSubsetPiRestrict hst F ell,
    fun p => ell ⟨p.1,(Finset.mem_sdiff.mp p.2).1⟩)
  invFun ell p := if hp : p.1 ∈ s then ell.1 ⟨p.1,hp⟩
    else ell.2 ⟨p.1,Finset.mem_sdiff.mpr ⟨p.2,hp⟩⟩
  left_inv ell := by
    funext p
    dsimp only [markedFiniteSubsetPiRestrict]
    split_ifs <;> rfl
  right_inv := by
    rintro ⟨ell,other⟩
    apply Prod.ext
    · funext p
      dsimp only [markedFiniteSubsetPiRestrict]
      simp only [dite_eq_left p.2]
    · funext p
      simp only [dite_eq_right (Finset.mem_sdiff.mp p.2).2]

theorem marked_finite_subset_pi_mean {α : Type*} [DecidableEq α]
    (s t : Finset α) (hst : s ⊆ t) (F : α → Type*)
    [∀ p,Fintype (F p)] [∀ p,Nonempty (F p)]
    (f : ((p : s) → F p.1) → ℝ) :
    (∑ ell : (p : t) → F p.1,f (markedFiniteSubsetPiRestrict hst F ell))/
        (Fintype.card ((p : t) → F p.1):ℝ) =
      (∑ ell : (p : s) → F p.1,f ell)/(Fintype.card ((p : s) → F p.1):ℝ) := by
  let e := markedFiniteSubsetPiEquiv s t hst F
  have hsum : (∑ ell : (p : t) → F p.1,f (markedFiniteSubsetPiRestrict hst F ell)) =
      (∑ ell : (p : s) → F p.1,f ell)*(Fintype.card ((p : ↥(t \ s)) → F p.1):ℝ) := by
    calc
      _ = ∑ pair : ((p : s) → F p.1) × ((p : ↥(t \ s)) → F p.1),f pair.1 :=
        Equiv.sum_comp e (fun pair => f pair.1)
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [← Finset.mul_sum,mul_comm,Finset.card_univ]
  have hcard : Fintype.card ((p : t) → F p.1) =
      Fintype.card ((p : s) → F p.1)*Fintype.card ((p : ↥(t \ s)) → F p.1) :=
    (Fintype.card_congr e).trans (Fintype.card_prod _ _)
  rw [hsum,hcard,Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast Fintype.card_ne_zero)

theorem markedMemoryIndependentLines_marginal (s t : Finset Nat.Primes) (hst : s ⊆ t)
    (f : MarkedMemoryIndependentLines s → ℝ) :
    (∑ ell : MarkedMemoryIndependentLines t,
        f (markedFiniteSubsetPiRestrict hst MarkedRawPrimeLine ell))/
        (Fintype.card (MarkedMemoryIndependentLines t):ℝ) =
      (∑ ell : MarkedMemoryIndependentLines s,f ell)/
        (Fintype.card (MarkedMemoryIndependentLines s):ℝ) := by
  let (p : Nat.Primes) : Nonempty (MarkedRawPrimeLine p) := ⟨markedVerticalProjectiveLine _⟩
  exact marked_finite_subset_pi_mean s t hst MarkedRawPrimeLine f

end ArtinMatthews
