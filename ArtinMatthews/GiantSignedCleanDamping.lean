module

public import ArtinMatthews.GiantSignedMemoryState
public import ArtinMatthews.GiantSignedCleanFiber
public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.GiantSignedCleanFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Both pending half-dampings act on the full, unbounded memory.
They commute with the active-list averages because they leave active labels untouched. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedPendingZeros {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (m : GiantSignedMemory P) : ℕ := by
  classical
  exact ∑ g, (Finset.univ.filter (fun i : Fin (m.1 g) => (m.2 g i).2 = 0)).card

def giantSignedPendingDamping {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ρ : ℝ) (m : GiantSignedMemory P) : ℝ := ρ ^ giantSignedPendingZeros m

theorem giantSignedPendingDamping_nonneg {B : Type*} [Fintype B] {P : B → Finset ℕ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (m : GiantSignedMemory P) :
    0 ≤ giantSignedPendingDamping ρ m := pow_nonneg hρ _

theorem giantSignedPendingDamping_le_one {B : Type*} [Fintype B] {P : B → Finset ℕ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (m : GiantSignedMemory P) :
    giantSignedPendingDamping ρ m ≤ 1 := pow_le_one₀ hρ hρ1

theorem giantSignedPendingDamping_norm {B : Type*} [Fintype B] {P : B → Finset ℕ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (m : GiantSignedMemory P) :
    ‖(giantSignedPendingDamping ρ m : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (giantSignedPendingDamping_nonneg hρ m)]
  exact giantSignedPendingDamping_le_one hρ hρ1 m

theorem giantSignedActiveMultiplier_slotAverage
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M : ℕ}
    (c : ℂ) (f : MarkedPhysicalMarking P M → ℂ) (a : MarkedPhysicalMarking P M) :
    idealSlotAverage (fun b => c * f b) a = c * idealSlotAverage f a := by
  unfold idealSlotAverage
  rw [← Finset.mul_sum]
  ring

theorem giantSignedWeightedEnergy_multiplier
    {X A : Type*} [Fintype X] [Fintype A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (d : X → ℂ) (hd : ∀ x, ‖d x‖ ≤ 1)
    (f : X → A → ℂ) :
    (∑ x, ∑ a, w a * ‖d x * f x a‖ ^ 2) ≤
      ∑ x, ∑ a, w a * ‖f x a‖ ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hw a)
  apply pow_le_pow_left₀ (norm_nonneg _) _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hd x)

def giantSignedDampedCleanFiberApply
    {I G J : Type*} [AddCommGroup G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (u : G)
    (dIn dOut : G → ℂ) (f : G → MarkedPhysicalMarking P (k+ell) → ℂ)
    (x : G) (a : MarkedPhysicalMarking P (k+ell)) : ℂ :=
  dIn x * giantSignedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u
    (fun y b => dOut y * f y b) x a

theorem giantSignedDampedCleanFiberApply_energy
    {I G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (activeMass : MarkedPhysicalMarking P (k+ell) → ℝ)
    (hMass : ∀ a, 0 ≤ activeMass a)
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ U : ℝ)
    (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (u : G)
    (dIn dOut : G → ℂ) (hIn : ∀ x, ‖dIn x‖ ≤ 1) (hOut : ∀ x, ‖dOut x‖ ≤ 1)
    (hIdeal : ∀ θ (h : MarkedPhysicalMarking P (k+ell) → ℂ), IdealSymmetric h →
      (∑ a, activeMass a *
        ‖idealOperatorWithLaws freshLaw auxLaw patterns C θ ζ K h a‖ ^ 2) ≤
          U ^ 2 * ∑ a, activeMass a * ‖h a‖ ^ 2)
    (f : G → MarkedPhysicalMarking P (k+ell) → ℂ)
    (hf : ∀ x, IdealSymmetric (f x)) :
    (∑ x, ∑ a, activeMass a *
      ‖giantSignedDampedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u
        dIn dOut f x a‖ ^ 2) ≤ U ^ 2 * ∑ x, ∑ a, activeMass a * ‖f x a‖ ^ 2 := by
  classical
  unfold giantSignedDampedCleanFiberApply
  calc
    _ ≤ ∑ x, ∑ a, activeMass a *
        ‖giantSignedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u
          (fun y b => dOut y * f y b) x a‖ ^ 2 :=
      giantSignedWeightedEnergy_multiplier activeMass hMass dIn hIn _
    _ ≤ U ^ 2 * ∑ x, ∑ a, activeMass a * ‖dOut x * f x a‖ ^ 2 :=
      giantSignedCleanFiberApply_energy_symmetric activeMass freshLaw auxLaw patterns C Θ ζ U K u
        hIdeal _ (fun x π a => congrArg (fun z => dOut x * z) (hf x π a))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (giantSignedWeightedEnergy_multiplier activeMass hMass dOut hOut f) (sq_nonneg U)

end
end ArtinMatthews
