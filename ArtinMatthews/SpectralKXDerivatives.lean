module

public import ArtinMatthews.SpectralKShiftedPointBound
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs


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
