module

public import ArtinMatthews.IdealPatternFreeCoordinates
public import ArtinMatthews.IdealPatternRowExpectation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual copied-coordinate row is a normalized product resampling. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedIdeal_base_resampling
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) (F : MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ b : MarkedPhysicalMarking P (k+ell), if IdealCopied C a b then
      (idealFreshTargetMass (fun j => markedHarmonicAtom (P j)) C b : ℂ) * F b else 0) =
      idealLabelExpectation P (k+ell) (fun z => F (idealMix (idealPatternFreeCoordinates C) a z)) := by
  classical
  let S : Finset (J × Fin (k+ell)) := idealPatternFreeCoordinates C
  have hfill (z : MarkedPhysicalMarking P (k+ell)) :
      idealMix S a z = idealFlattenLabels.symm
        (finiteProductFill S (idealFlattenLabels a) (idealFullSelectedLabels S z)) := by
    funext j i
    simp only [idealMix, idealFlattenLabels, Equiv.coe_fn_symm_mk, finiteProductFill,
      idealFullSelectedLabels]
    split_ifs <;> rfl
  rw [idealPattern_target_sum_eq_fresh]
  symm
  calc
    _ = idealLabelExpectation P (k+ell) (fun z => F (idealFlattenLabels.symm
        (finiteProductFill S (idealFlattenLabels a) (idealFullSelectedLabels S z)))) := by
      congr 1
      funext z
      rw [hfill]
    _ = ∑ y : IdealSelectedLabels (idealFullSelectedBands P S),
        (idealSelectedMass (idealFullSelectedBands P S) y : ℂ) *
          F (idealFlattenLabels.symm (finiteProductFill S (idealFlattenLabels a) y)) :=
      idealFullSelected_marginal P hV S (fun y =>
        F (idealFlattenLabels.symm (finiteProductFill S (idealFlattenLabels a) y)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      unfold idealSelectedMass finiteProductMarginalMass idealFullSelectedBands
      rw [Complex.ofReal_prod]

end
end ArtinMatthews
