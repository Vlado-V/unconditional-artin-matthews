module

public import ArtinMatthews.GiantSignedMemoryState
public import ArtinMatthews.IdealLabelOperator
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

/-! Literal product-density identities for the active and fresh laws. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset ℕ}

theorem giantSignedActiveMass_mul {M : ℕ} (μ r : ∀ j, P j → ℝ)
    (a : MarkedPhysicalMarking P M) :
    giantSignedActiveMass (fun j p => μ j p * r j p) a =
      giantSignedActiveMass μ a * giantSignedActiveMass r a := by
  unfold giantSignedActiveMass
  simp only [Finset.prod_mul_distrib]

theorem idealFreshTargetMass_mul {k ell : ℕ} (μ r : ∀ j, P j → ℝ)
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell)) :
    idealFreshTargetMass (fun j p => μ j p * r j p) C a =
      idealFreshTargetMass μ C a * idealFreshTargetMass r C a := by
  unfold idealFreshTargetMass
  simp only [Finset.prod_mul_distrib]

theorem giantSignedActiveMass_one_le {M : ℕ} (r : ∀ j, P j → ℝ)
    (hr : ∀ j p, 1 ≤ r j p) (a : MarkedPhysicalMarking P M) :
    1 ≤ giantSignedActiveMass r a := by
  unfold giantSignedActiveMass
  exact Finset.one_le_prod₀ (fun j _ => Finset.one_le_prod₀ (fun i _ => hr j (a j i)))

theorem idealFreshTargetMass_one_le {k ell : ℕ} (r : ∀ j, P j → ℝ)
    (hr : ∀ j p, 1 ≤ r j p) (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) :
    1 ≤ idealFreshTargetMass r C a := by
  unfold idealFreshTargetMass
  exact Finset.one_le_prod₀ (fun j _ => Finset.one_le_prod₀ (fun i _ => hr j (a j _)))

theorem giantSignedActiveMass_upper {M : ℕ} (r : ∀ j, P j → ℝ)
    (hr : ∀ j p, 0 ≤ r j p) (R : ℝ) (hR : ∀ j p, r j p ≤ R)
    (a : MarkedPhysicalMarking P M) :
    giantSignedActiveMass r a ≤ R ^ (Fintype.card J * M) := by
  unfold giantSignedActiveMass
  calc
    _ ≤ ∏ _j : J, R ^ M := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact Finset.prod_nonneg fun i _ => hr j (a j i)
      · intro j _
        calc
          _ ≤ ∏ _i : Fin M, R := Finset.prod_le_prod₀ (fun i _ => hr j (a j i))
            (fun i _ => hR j (a j i))
          _ = _ := by simp
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

theorem idealFreshTargetMass_upper {k ell : ℕ} (r : ∀ j, P j → ℝ)
    (hr : ∀ j p, 0 ≤ r j p) (R : ℝ) (hR : ∀ j p, r j p ≤ R)
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell)) :
    idealFreshTargetMass r C a ≤ ∏ j, R ^ ((C j).card + ell) := by
  unfold idealFreshTargetMass
  apply Finset.prod_le_prod₀
  · intro j _
    exact Finset.prod_nonneg fun i _ => hr j (a j _)
  · intro j _
    calc
      _ ≤ ∏ _i : GiantTwoSidedPatternFreeSlots (C j) ell, R :=
        Finset.prod_le_prod₀ (fun i _ => hr j (a j _)) (fun i _ => hR j (a j _))
      _ = _ := by simp [GiantTwoSidedPatternFreeSlots]

theorem giantSignedTilt_activeEnergy_le [DecidableEq J] {M : ℕ} (μ r : ∀ j, P j → ℝ)
    (hμ : ∀ j p, 0 ≤ μ j p) (hr : ∀ j p, 0 ≤ r j p)
    (R : ℝ) (hR : ∀ j p, r j p ≤ R) (f : MarkedPhysicalMarking P M → ℂ) :
    (∑ a, giantSignedActiveMass (fun j p => μ j p * r j p) a * ‖f a‖ ^ 2) ≤
      R ^ (Fintype.card J * M) * ∑ a, giantSignedActiveMass μ a * ‖f a‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [giantSignedActiveMass_mul]
  have hm : 0 ≤ giantSignedActiveMass μ a :=
    Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun i _ => hμ j (a j i)
  have h := mul_le_mul_of_nonneg_left (giantSignedActiveMass_upper r hr R hR a)
    (mul_nonneg hm (sq_nonneg ‖f a‖))
  nlinarith

end
end ArtinMatthews
