module

public import ArtinMatthews.MarkedMinorArcBanKernel
public import ArtinMatthews.MarkedMinorArcBanCollision
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

/-! Actual finite ban-removal coefficient rows, with the collision cost derived. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def markedBanRemovedCoefficient (bad : Prop) (c : ℂ) : ℂ := by
  classical
  exact c-(if bad then 0 else c)

theorem markedBanRemovedCoefficient_norm (bad : Prop) [Decidable bad] (c : ℂ) :
    ‖markedBanRemovedCoefficient bad c‖ = if bad then ‖c‖ else 0 := by
  classical
  by_cases h : bad <;> simp [markedBanRemovedCoefficient,h]

def markedBanRowError {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (q x : ℝ) {M : ℕ}
    (source : (j : J) → Fin M → ↥(markedLogPowerBand (e j) x))
    (z : ℤ × ℤ) (D b : ℤ) (ψ : ℝ → ℂ) (Q Y : ℝ)
    (V : MarkedFreshPrimeTuple e x → Finset (ℤ × ℤ))
    (test : MarkedFreshPrimeTuple e x → (ℤ × ℤ) → ℂ) : ℝ :=
  ∑ t, markedFreshTiltedLaw e q x t * ∑ v ∈ V t,
    ‖markedBanRemovedCoefficient (MarkedBanFreshCollision source t)
      (test t v*markedBanEdgeKernel ψ Q Y b (markedFreshIntegerProduct e x t)
        (markedBanNormalizedDet z D v))‖

def markedBanErrorConstant (K : ℕ) (A W : ℝ) : ℝ :=
  (33*W*(8*A+5))*(2:ℝ)^K*K*(2/Real.log 2)

/-- The literal removed coefficient row has the source collision saving.
The premises describe actual finite positions and bounded endpoint tests;
no row estimate is supplied as an input. -/
theorem markedBan_actual_row_error_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (M : ℕ)
      (source : (j : J) → Fin M → ↥(markedLogPowerBand (e j) x)) (q r : ℝ)
      (z w : ℤ × ℤ) (D b : ℤ) (ψ : ℝ → ℂ) (Q Y A W : ℝ)
      (V : MarkedFreshPrimeTuple e x → Finset (ℤ × ℤ))
      (test : MarkedFreshPrimeTuple e x → (ℤ × ℤ) → ℂ),
      0 ≤ q → q ≤ 1 → markedMinorIntegerDet z w=1 → markedMinorIntegerTau r z ≠ 0 →
      1 ≤ Q → 1 ≤ Y → 0 ≤ A → 0 ≤ W → (∀ u, ‖ψ u‖ ≤ W) →
      (∀ u, ψ u ≠ 0 → |u| ≤ A) →
      (∀ t v, v ∈ V t → D ∣ markedMinorIntegerDet z v ∧
        |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16) →
      (∀ t v, v ∈ V t → ‖test t v‖ ≤ 1) →
      markedBanRowError e q x source z D b ψ Q Y V test ≤
        markedBanErrorConstant (Fintype.card J) A W*M*Q^3*
          Real.exp (-((Real.log x)^(1/10:ℝ))) := by
  classical
  filter_upwards [markedBan_actual_collision_mass_eventually e he hinj,
    marked_actual_tilted_atom_comparison_eventually e he] with x hcollision hatom
  intro M source q r z w D b ψ Q Y A W V test hq0 hq1 hd hz hQ hY hA hW hψ hsupp hV htest
  let B : ℝ := (33*W*(8*A+5))*Q^3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hν (t : MarkedFreshPrimeTuple e x) : 0 ≤ markedFreshTiltedLaw e q x t :=
    Finset.prod_nonneg (fun j _ => (hatom q hq0 hq1 j (t j)).1)
  have hpoint (t : MarkedFreshPrimeTuple e x) :
      markedFreshTiltedLaw e q x t * ∑ v ∈ V t,
        ‖markedBanRemovedCoefficient (MarkedBanFreshCollision source t)
          (test t v*markedBanEdgeKernel ψ Q Y b (markedFreshIntegerProduct e x t)
            (markedBanNormalizedDet z D v))‖ ≤
      (if MarkedBanFreshCollision source t then (1:ℝ) else 0)*markedFreshTiltedLaw e q x t*B := by
    by_cases ht : MarkedBanFreshCollision source t
    · simp only [markedBanRemovedCoefficient_norm,ht,ite_true,one_mul]
      exact mul_le_mul_of_nonneg_left
        (markedBan_kernel_row_bound_polynomial r z w D b (markedFreshIntegerProduct e x t)
          hd hz (V t) (hV t) ψ hQ hY hA hW hψ hsupp (test t) (htest t)) (hν t)
    · simp only [markedBanRemovedCoefficient_norm,ht,ite_false,Finset.sum_const_zero,mul_zero,zero_mul]
      exact le_rfl
  calc
    _ ≤ ∑ t, (if MarkedBanFreshCollision source t then (1:ℝ) else 0)*markedFreshTiltedLaw e q x t*B :=
      Finset.sum_le_sum (fun t _ => hpoint t)
    _ = markedEventMass (markedFreshTiltedLaw e q x) (MarkedBanFreshCollision source)*B :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ ((2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ)*M*
        ((2/Real.log 2)*Real.exp (-((Real.log x)^(1/10:ℝ)))))*B :=
      mul_le_mul_of_nonneg_right (hcollision M source q hq0 hq1) hB
    _ = _ := by unfold markedBanErrorConstant; dsimp [B]; ring

end ArtinMatthews
