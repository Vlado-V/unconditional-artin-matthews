module

public import ArtinMatthews.GaussianCoordinateFiniteSieve
public import ArtinMatthews.VaryingKummerAnalyticCoordinateLifts
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Finset VaryingKummerAnalytic
noncomputable section
variable {β ι : Type*} [Fintype β]

/-- Separation modulo the actual integer coordinate lattice gives separation
of every distinct lift, including integer translates of the same label. -/
theorem coordinateGaussianLift_separated_of_modular {Q : ℝ} (hQ : 1 ≤ Q)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ∀ k : β → ℤ,
      1/Q ≤ ‖(fun b => x i b-x j b+(k b:ℝ))‖) :
    ∀ u v : {i // i ∈ P} × (β → ℤ), u ≠ v →
      1/Q ≤ ‖coordinateGaussianLift x (u.1.val,u.2)-
        coordinateGaussianLift x (v.1.val,v.2)‖ := by
  have hs : ∀ i j : {i // i ∈ P}, i ≠ j → ∀ k : β → ℤ,
      1/Q ≤ ‖(fun b => x i.val b-x j.val b+(k b:ℝ))‖ := by
    intro i j hij k
    exact hsep i.val i.property j.val j.property (fun h => hij (Subtype.ext h)) k
  exact coordinateLift_separated hQ (fun i : {i // i ∈ P} => x i.val) hs

/-- Finite additive large sieve with only actual modular frequency separation
and the actual squared-coordinate support bound as geometric hypotheses. -/
theorem coordinate_modular_primal_sieve {Q a R : ℝ} (hQ : 1 ≤ Q) (ha : 0 < a)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ∀ k : β → ℤ,
      1/Q ≤ ‖(fun b => x i b-x j b+(k b:ℝ))‖)
    (N : Finset (β → ℤ)) (hN : ∀ n ∈ N, (∑ b, (n b:ℝ)^2) ≤ R)
    (v : (β → ℤ) → ℂ) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n*coordinatePhase (x p) n‖^2) ≤
      coordinateAdditiveSieveBound β Q a R*∑ n ∈ N, ‖v n‖^2 :=
  coordinate_finite_primal_sieve (by linarith) ha P x
    (coordinateGaussianLift_separated_of_modular hQ P x hsep) N hN v

/-- Dual form of the same modular additive sieve. -/
theorem coordinate_modular_dual_sieve {Q a R : ℝ} (hQ : 1 ≤ Q) (ha : 0 < a)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ∀ k : β → ℤ,
      1/Q ≤ ‖(fun b => x i b-x j b+(k b:ℝ))‖)
    (N : Finset (β → ℤ)) (hN : ∀ n ∈ N, (∑ b, (n b:ℝ)^2) ≤ R)
    (v : ι → ℂ) :
    (∑ n ∈ N, ‖∑ p ∈ P, v p*coordinatePhase (x p) n‖^2) ≤
      coordinateAdditiveSieveBound β Q a R*∑ p ∈ P, ‖v p‖^2 :=
  coordinate_finite_dual_sieve (by linarith) ha P x
    (coordinateGaussianLift_separated_of_modular hQ P x hsep) N hN v

end
end ArtinMatthews
