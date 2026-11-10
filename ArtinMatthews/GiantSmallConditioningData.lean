module

public import ArtinMatthews.GiantTwoSidedResidueState
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

/-! The small conditioning map uses the original ordered prefix and tail,
zero-extends actual small states, and keeps the source normalization. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} {P : J → Finset ℕ} {k ell : ℕ}

def giantSmallAppend (d : MarkedPhysicalMarking P k) (r : MarkedPhysicalMarking P ell) :
    MarkedPhysicalMarking P (k + ell) := fun j => Fin.append (d j) (r j)

def giantSmallAppendEquiv (P : J → Finset ℕ) (k ell : ℕ) :
    MarkedPhysicalMarking P k × MarkedPhysicalMarking P ell ≃
      MarkedPhysicalMarking P (k + ell) where
  toFun dr := giantSmallAppend dr.1 dr.2
  invFun a := (fun j i => a j (Fin.castAdd ell i), fun j i => a j (Fin.natAdd k i))
  left_inv dr := by
    apply Prod.ext <;> funext j i <;> simp [giantSmallAppend]
  right_inv a := by
    funext j
    exact Fin.append_castAdd_natAdd

variable [Fintype J]

def GiantSmallStateCondition (y : GiantTwoSidedFullResidue P)
    (a : MarkedPhysicalMarking P (k + ell)) : Prop :=
  MarkedPhysicalMarkingDistinct a ∧
    ∀ j i, y (giantTwoSidedResidueIndex j (a j i)) = 0

def giantSmallStateValue {E : Type*} [Zero E]
    (w : GiantTwoSidedResidueState P (k + ell) → E)
    (y : GiantTwoSidedFullResidue P) (a : MarkedPhysicalMarking P (k + ell)) : E :=
  if h : GiantSmallStateCondition y a then w ⟨(y, a), h⟩ else 0

def giantSmallConditioningTails [DecidableEq J]
    (y : GiantTwoSidedFullResidue P) (d : MarkedPhysicalMarking P k) :
    Finset (MarkedPhysicalMarking P ell) :=
  univ.filter (fun r => GiantSmallStateCondition y (giantSmallAppend d r))

theorem giantSmallAppend_sum [DecidableEq J] {E : Type*} [AddCommMonoid E]
    (f : MarkedPhysicalMarking P (k + ell) → E) :
    (∑ d : MarkedPhysicalMarking P k, ∑ r : MarkedPhysicalMarking P ell,
      f (giantSmallAppend d r)) = ∑ a : MarkedPhysicalMarking P (k + ell), f a := by
  exact (Fintype.sum_prod_type (fun dr : MarkedPhysicalMarking P k ×
    MarkedPhysicalMarking P ell => f (giantSmallAppend dr.1 dr.2))).symm.trans
      ((giantSmallAppendEquiv P k ell).sum_comp f)

theorem giantSmallStateValue_sum [DecidableEq J]
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]
    {E : Type*} [AddCommMonoid E] (w : GiantTwoSidedResidueState P (k + ell) → E) :
    (∑ y : GiantTwoSidedFullResidue P, ∑ a : MarkedPhysicalMarking P (k + ell),
      giantSmallStateValue w y a) = ∑ s : GiantTwoSidedResidueState P (k + ell), w s := by
  rw [← Fintype.sum_prod_type (fun ya : GiantTwoSidedFullResidue P ×
    MarkedPhysicalMarking P (k + ell) => giantSmallStateValue w ya.1 ya.2)]
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective w
    (fun ya => giantSmallStateValue w ya.1 ya.2)
  · intro ya hy
    have hn : ¬GiantSmallStateCondition ya.1 ya.2 := by
      intro h
      exact hy ⟨⟨ya, h⟩, rfl⟩
    exact dite_eq_right hn
  · intro s
    have hs : GiantSmallStateCondition s.val.1 s.val.2 := s.property
    rw [giantSmallStateValue, dite_eq_left hs]

def giantSmallConditioningNormalization (P : J → Finset ℕ) (k ell : ℕ) : ℝ :=
  ∏ j, (bandReciprocalMass (P j)) ^ (-(k : ℝ) / 2 - (ell : ℝ))

def giantSmallTailMass (P : J → Finset ℕ) (ell : ℕ) : ℝ :=
  ∏ j, (bandReciprocalMass (P j))⁻¹ ^ ell

theorem giantSmallConditioningNormalization_nonneg
    (hV : ∀ j, 0 ≤ bandReciprocalMass (P j)) :
    0 ≤ giantSmallConditioningNormalization P k ell :=
  prod_nonneg fun j _ => Real.rpow_nonneg (hV j) _

theorem giantSmallConditioningNormalization_sq
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) :
    (giantSmallConditioningNormalization P k ell) ^ 2 =
      markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k + ell) *
        giantSmallTailMass P ell := by
  unfold giantSmallConditioningNormalization markedPhysicalMass giantSmallTailMass
  rw [← prod_pow, ← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  calc
    ((bandReciprocalMass (P j)) ^ (-(k : ℝ) / 2 - (ell : ℝ))) ^ 2 =
        (bandReciprocalMass (P j)) ^ ((-(k : ℝ) / 2 - (ell : ℝ)) * (2 : ℝ)) :=
      (Real.rpow_mul_natCast (hV j).le _ 2).symm
    _ = (bandReciprocalMass (P j)) ^ (-(((k + ell) + ell : ℕ) : ℝ)) := by
      congr 1
      push_cast
      ring
    _ = (bandReciprocalMass (P j))⁻¹ ^ ((k + ell) + ell) := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
    _ = _ := pow_add _ _ _

def giantSmallConditioningMap [DecidableEq J] (P : J → Finset ℕ) (k ell : ℕ)
    (q : ℝ) (d : MarkedPhysicalMarking P k)
    (w : GiantTwoSidedResidueState P (k + ell) → ℂ)
    (y : GiantTwoSidedFullResidue P) : ℂ :=
  (giantSmallConditioningNormalization P k ell : ℂ) *
    (giantTwoSidedResidueDamping P (k + ell) q y : ℂ) *
      ∑ r : MarkedPhysicalMarking P ell, giantSmallStateValue w y (giantSmallAppend d r)

def giantSmallStateEnergy [DecidableEq J]
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]
    (w : GiantTwoSidedResidueState P (k + ell) → ℂ) : ℝ :=
  giantTwoSidedResidueHaarStateMass P (k + ell) * ∑ s, ‖w s‖ ^ 2

def giantSmallResidueEnergy
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]
    (f : GiantTwoSidedFullResidue P → ℂ) : ℝ :=
  (Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹ * ∑ y, ‖f y‖ ^ 2

end
end ArtinMatthews
