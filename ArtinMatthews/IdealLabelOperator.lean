module

public import ArtinMatthews.GiantTwoSidedPatternCompletions
public import ArtinMatthews.GiantTwoSidedLabelOffsets
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

/-! The literal residual ideal row operator. Repeated prime labels are
allowed, shared slots are copied, and all fresh laws remain explicit. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealFreshTargetMass {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell : ℕ}
    (ν : ∀ j,↥(P j) → ℝ) (C : J → Finset (Fin k))
    (b : MarkedPhysicalMarking P (k+ell)) : ℝ :=
  ∏ j,∏ i : GiantTwoSidedPatternFreeSlots (C j) ell,
    ν j (b j (giantTwoSidedPatternFreeSlot (C j) ell i))

def idealAuxiliaryMass {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
    (ν : ∀ j,↥(P j) → ℝ) {C : J → Finset (Fin k)}
    (a : GiantTwoSidedPatternAuxiliary P C) : ℝ :=
  ∏ j,∏ i : ↥(C j),ν j (a j i)

def IdealCopied {J : Type*} {P : J → Finset ℕ} {k ell : ℕ}
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P (k+ell)) : Prop :=
  ∀ j (i : Fin k),i∉C j → b j (Fin.castAdd ell i)=a j (Fin.castAdd ell i)

def idealAdditivePhase (Θ : ℝ) (D : ℕ) : ℂ :=
  Complex.exp (((2*Real.pi*Θ*(D:ℝ):ℝ):ℂ)*Complex.I)

theorem idealAdditivePhase_norm (Θ : ℝ) (D : ℕ) : ‖idealAdditivePhase Θ D‖=1 := by
  simp [idealAdditivePhase,Complex.norm_exp]

def idealPatternApplyWithLaws {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j,↥(P j) → ℝ) (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (f : MarkedPhysicalMarking P (k+ell) → ℂ)
    (a : MarkedPhysicalMarking P (k+ell)) : ℂ :=
  ∑ aux : GiantTwoSidedPatternAuxiliary P C,
    (idealAuxiliaryMass auxLaw aux:ℂ)*
      ∑ b : MarkedPhysicalMarking P (k+ell),if IdealCopied C a b then
        (idealFreshTargetMass freshLaw C b:ℂ)*K a b aux*
          ((giantTwoSidedPatternCopiedProduct C a*giantTwoSidedPatternAuxiliaryProduct aux:ℕ):ℂ)^
            ((ζ:ℂ)*Complex.I)*
          idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct C a*giantTwoSidedPatternAuxiliaryProduct aux)*f b
      else 0

def idealSlotAverage {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (f : MarkedPhysicalMarking P M → ℂ)
    (a : MarkedPhysicalMarking P M) : ℂ :=
  ((Fintype.card (J → Equiv.Perm (Fin M)):ℂ)⁻¹)*
    ∑ π : J → Equiv.Perm (Fin M),f (giantTwoSidedPermuteLabels π a)

def idealOperatorWithLaws {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j,↥(P j) → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) : MarkedPhysicalMarking P (k+ell) → ℂ :=
  idealSlotAverage (fun a => ∑ ν∈patterns,
    idealPatternApplyWithLaws freshLaw auxLaw (C ν) Θ ζ (K ν) (idealSlotAverage f) a)

def idealOperator {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) : MarkedPhysicalMarking P (k+ell) → ℂ :=
  idealOperatorWithLaws (fun j => markedHarmonicAtom (P j))
    (fun j => markedHarmonicAtom (P j)) patterns C Θ ζ K f

end
end ArtinMatthews
