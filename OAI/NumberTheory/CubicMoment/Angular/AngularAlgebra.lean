module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicGram.Definitions
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import OAI.NumberTheory.CubicGram.Coordinates


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-!
# Algebra of fixed angular prime moments

The angular weight is the phase of a nonzero Eisenstein integer raised to
an integer power.  These elementary facts ensure that fixed angular
weights preserve absolute values and distribute through finite prime sums.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

/-- The bias constant in the manuscript is strictly positive. -/
theorem cStar_pos : 0 < cStar := by
  unfold cStar
  positivity

/-- The scale of the first moment is positive beyond one. -/
theorem firstMomentScale_pos {X : ℝ} (hX : 1 < X) : 0 < firstMomentScale X := by
  unfold firstMomentScale
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos hX)

@[simp] theorem theta_zero (a : Eisenstein) : theta 0 a = 1 := by
  simp [theta]

@[simp] theorem theta_one (ℓ : ℤ) : theta ℓ (1 : Eisenstein) = 1 := by
  simp [theta]

@[simp] theorem theta_mul (ℓ : ℤ) (a b : Eisenstein) :
    theta ℓ (a * b) = theta ℓ a * theta ℓ b := by
  simp only [theta, Subalgebra.coe_mul, norm_mul, Complex.ofReal_mul]
  rw [mul_div_mul_comm, mul_zpow]

@[simp] theorem norm_theta {a : Eisenstein} (ha : a ≠ 0) (ℓ : ℤ) :
    ‖theta ℓ a‖ = 1 := by
  have ha' : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  simp [theta, norm_zpow, ha']

@[simp] theorem norm_theta_mul {a : Eisenstein} (ha : a ≠ 0) (ℓ : ℤ) (z : ℂ) :
    ‖theta ℓ a * z‖ = ‖z‖ := by
  rw [norm_mul, norm_theta ha, one_mul]

@[simp] theorem theta_add (ℓ m : ℤ) {a : Eisenstein} (ha : a ≠ 0) :
    theta (ℓ + m) a = theta ℓ a * theta m a := by
  have ha' : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  exact zpow_add₀ (div_ne_zero ha' (by exact_mod_cast norm_ne_zero_iff.mpr ha')) _ _

@[simp] theorem primeCutoffSum_add (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p + g p) X =
      primeCutoffSum f X + primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_add_distrib]

@[simp] theorem primeCutoffSum_sub (f g : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => f p - g p) X =
      primeCutoffSum f X - primeCutoffSum g X := by
  simp only [primeCutoffSum_eq_sum, Finset.sum_sub_distrib]

@[simp] theorem primeCutoffSum_const_mul (z : ℂ) (f : Eisenstein → ℂ) (X : ℝ) :
    primeCutoffSum (fun p => z * f p) X = z * primeCutoffSum f X := by
  simp only [primeCutoffSum_eq_sum, Finset.mul_sum]

/-- The elementary prime model in the fixed angular mode `ℓ`. -/
def angularPrimeModel (ℓ : ℤ) (p : Eisenstein) : ℂ :=
  theta ℓ p * (cStar * norm p ^ (-1 / 6 : ℝ) : ℝ)

/-- The prime Gauss-sum moment in the fixed angular mode `ℓ`. -/
def angularPrimeMoment (ℓ : ℤ) (X : ℝ) : ℂ :=
  primeCutoffSum (fun p => theta ℓ p * gaussAtPrime p) X

/-- The difference between the Gauss-sum moment and its elementary model. -/
def angularPrimeDifference (ℓ : ℤ) (X : ℝ) : ℂ :=
  primeCutoffSum (fun p => theta ℓ p *
    (gaussAtPrime p - (cStar * norm p ^ (-1 / 6 : ℝ) : ℝ))) X

theorem angularPrimeDifference_eq_sub (ℓ : ℤ) (X : ℝ) :
    angularPrimeDifference ℓ X =
      angularPrimeMoment ℓ X - primeCutoffSum (angularPrimeModel ℓ) X := by
  simp only [angularPrimeDifference, angularPrimeMoment, mul_sub, primeCutoffSum_sub]
  rfl

/-- Angular comparison and the model prime-number theorem imply angular
cancellation by subtraction. -/
theorem angularCancellation_of_comparison
    (hcomparison : AngularComparisonStatement)
    (hmodel : ∀ ℓ : ℤ, ℓ ≠ 0 → Asymptotics.IsLittleO Filter.atTop
      (primeCutoffSum (angularPrimeModel ℓ)) firstMomentScale) :
    AngularCancellationStatement := by
  intro ℓ hℓ
  have h := (hcomparison ℓ).add (hmodel ℓ hℓ)
  have heq : (fun X => angularPrimeDifference ℓ X +
      primeCutoffSum (angularPrimeModel ℓ) X) = angularPrimeMoment ℓ := by
    funext X
    rw [angularPrimeDifference_eq_sub, sub_add_cancel]
  change Asymptotics.IsLittleO Filter.atTop (angularPrimeMoment ℓ) firstMomentScale
  change Asymptotics.IsLittleO Filter.atTop
    (fun X => angularPrimeDifference ℓ X + primeCutoffSum (angularPrimeModel ℓ) X)
    firstMomentScale at h
  rwa [heq] at h

end CubicFirstMoment

end

end OAI
