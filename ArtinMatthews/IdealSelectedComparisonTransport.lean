module

public import ArtinMatthews.IdealCellPhaseComparison
public import ArtinMatthews.IdealSelectedFibers
public import ArtinMatthews.IdealSelectedKernelTransport
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

/-! The complete bilinear comparison expression, its arbitrary tests,
and both harmonic energies are unchanged by selected-slot reindexing. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealSelectedComparisonForm {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : I → Finset ℕ) (R : J → Finset ℕ) (Q : ℕ) (h ξ ζ α : ℝ)
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ) : ℂ :=
  ∑ x,(idealSelectedMass P x:ℂ)*f x*∑ y,(idealSelectedMass R y:ℂ)*g y*
    (idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y)-
      idealFullCellPhaseAverage P R Q h ξ ζ α x y)

theorem idealSelectedComparisonForm_transport {I J I' J' : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    (P : I → Finset ℕ) (R : J → Finset ℕ) (P' : I' → Finset ℕ) (R' : J' → Finset ℕ)
    (e : IdealSelectedLabels P ≃ IdealSelectedLabels P')
    (d : IdealSelectedLabels R ≃ IdealSelectedLabels R')
    (hmP : ∀ a,idealSelectedMass P a=idealSelectedMass P' (e a))
    (hpP : ∀ a,idealSelectedProduct a=idealSelectedProduct (e a))
    (hmR : ∀ a,idealSelectedMass R a=idealSelectedMass R' (d a))
    (hpR : ∀ a,idealSelectedProduct a=idealSelectedProduct (d a))
    (Q : ℕ) (h ξ ζ α : ℝ) (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ) :
    idealSelectedComparisonForm P R Q h ξ ζ α f g=
      idealSelectedComparisonForm P' R' Q h ξ ζ α (fun a => f (e.symm a)) (fun a => g (d.symm a)) := by
  unfold idealSelectedComparisonForm
  rw [← e.symm.sum_comp]
  apply sum_congr rfl
  intro x _
  rw [hmP,Equiv.apply_symm_apply]
  congr 1
  rw [← d.symm.sum_comp]
  apply sum_congr rfl
  intro y _
  rw [hmR,hpP,hpR,idealFullCellPhaseAverage_transport P R P' R' e d hmP hpP hmR hpR,
    Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem idealSelectedComparisonForm_sigma {G H : Type*}
    [Fintype G] [DecidableEq G] [Fintype H] [DecidableEq H]
    (P : G → Finset ℕ) (R : H → Finset ℕ) {M N : ℕ}
    (S : Finset (G × Fin M)) (T : Finset (H × Fin N))
    (Q : ℕ) (h ξ ζ α : ℝ)
    (f : IdealSelectedLabels (idealResidualBands P S) → ℂ)
    (g : IdealSelectedLabels (idealResidualBands R T) → ℂ) :
    idealSelectedComparisonForm (idealResidualBands P S) (idealResidualBands R T) Q h ξ ζ α f g=
      idealSelectedComparisonForm
        (fun v : Σ a,Fin (idealResidualFreeSlots S a).card => P v.1)
        (fun v : Σ b,Fin (idealResidualFreeSlots T b).card => R v.1) Q h ξ ζ α
        (fun a => f ((idealSelectedSigmaFinEquiv P S).symm a))
        (fun a => g ((idealSelectedSigmaFinEquiv R T).symm a)) :=
  idealSelectedComparisonForm_transport _ _ _ _ (idealSelectedSigmaFinEquiv P S)
    (idealSelectedSigmaFinEquiv R T) (idealSelectedSigmaFin_mass P S) (idealSelectedSigmaFin_product P S)
    (idealSelectedSigmaFin_mass R T) (idealSelectedSigmaFin_product R T) Q h ξ ζ α f g

end
end ArtinMatthews
