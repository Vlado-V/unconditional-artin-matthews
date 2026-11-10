module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralKDerivativeAdjacentOrder
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

/-! Every physical derivative of the genuine Schlaefli K kernel is the
finite adjacent-order recurrence. The recursive functions are identified
with the actual iterated derivatives on the positive ray. -/

noncomputable section
open Set Filter
open scoped Topology
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralKXDerivative : ℕ → ℂ → ℝ → ℂ
  | 0,ν => schlafliBesselK ν
  | n+1,ν => fun x => -(1/2 : ℂ)*(spectralKXDerivative n (ν-1) x+spectralKXDerivative n (ν+1) x)

@[simp] theorem spectralKXDerivative_zero (ν : ℂ) (x : ℝ) :
    spectralKXDerivative 0 ν x = schlafliBesselK ν x := rfl

theorem spectralKXDerivative_succ (n : ℕ) (ν : ℂ) (x : ℝ) :
    spectralKXDerivative (n+1) ν x =
      -(1/2 : ℂ)*(spectralKXDerivative n (ν-1) x+spectralKXDerivative n (ν+1) x) := rfl

theorem spectralKXDerivative_hasDerivAt (n : ℕ) (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (spectralKXDerivative n ν) (spectralKXDerivative (n+1) ν x) x := by
  induction n generalizing ν with
  | zero =>
    have h := (schlafliBesselK_hasDerivAt ν x hx).differentiableAt.hasDerivAt
    rw [schlafliBesselK_deriv_adjacent_order ν hx] at h
    exact h
  | succ n ih =>
    change HasDerivAt
      (fun y => -(1/2 : ℂ)*(spectralKXDerivative n (ν-1) y+spectralKXDerivative n (ν+1) y))
      (-(1/2 : ℂ)*(spectralKXDerivative (n+1) (ν-1) x+spectralKXDerivative (n+1) (ν+1) x)) x
    exact ((ih (ν-1)).add (ih (ν+1))).const_mul (-(1/2 : ℂ))

theorem spectralKXDerivative_deriv (n : ℕ) (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    deriv (spectralKXDerivative n ν) x = spectralKXDerivative (n+1) ν x :=
  (spectralKXDerivative_hasDerivAt n ν x hx).deriv

theorem schlafliBesselK_iteratedDeriv_eq (n : ℕ) (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (schlafliBesselK ν) x = spectralKXDerivative n ν x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (schlafliBesselK ν) =ᶠ[𝓝 x] spectralKXDerivative n ν := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact ih y hy
    exact he.deriv_eq.trans (spectralKXDerivative_deriv n ν x hx)

theorem schlafliBesselK_iteratedDeriv_hasDerivAt (n : ℕ) (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (iteratedDeriv n (schlafliBesselK ν))
      (spectralKXDerivative (n+1) ν x) x := by
  apply (spectralKXDerivative_hasDerivAt n ν x hx).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact schlafliBesselK_iteratedDeriv_eq n ν y hy

theorem schlafliBesselK_iteratedDeriv_continuousOn (n : ℕ) (ν : ℂ) :
    ContinuousOn (iteratedDeriv n (schlafliBesselK ν)) (Ioi (0 : ℝ)) := by
  intro x hx
  exact (schlafliBesselK_iteratedDeriv_hasDerivAt n ν x hx).continuousAt.continuousWithinAt

end ArtinMatthews
