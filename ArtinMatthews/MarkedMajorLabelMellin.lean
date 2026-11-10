module

public import ArtinMatthews.MarkedMajorMellinIsolationBase
public import ArtinMatthews.MarkedSparsePrimeMoments
public import ArtinMatthews.MarkedMajorMellinIsolation
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite Mellin separation of the isolated prime and the remaining
label product. All integrals are the normalized Fourier transform of the
given compact cutoff; no transform or decay assumption is introduced. -/
namespace ArtinMatthews
open Finset MeasureTheory
open scoped ContDiff

theorem markedMajorLabel_mellin_phase {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    {Y : ℝ} (hY : 0 < Y) (t ξ : ℝ) :
    Complex.exp (Complex.I*(ξ:ℂ)*(Real.log ((p*n:ℕ)/Y):ℂ))*markedPrimePhase (p*n) t =
      Complex.exp (-(Complex.I*(ξ:ℂ)*(Real.log Y:ℂ)))*
        markedPrimePhase p (t+ξ)*markedPrimePhase n (t+ξ) := by
  unfold markedPrimePhase
  rw [Nat.cast_mul,Real.log_div (mul_ne_zero (by exact_mod_cast hp.ne')
    (by exact_mod_cast hn.ne')) hY.ne',Real.log_mul (by exact_mod_cast hp.ne')
    (by exact_mod_cast hn.ne')]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem markedMajorLabel_finite_mellin
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Set.Icc a b)
    (S R : Finset ℕ) (hS : ∀ p ∈ S,0 < p) (hR : ∀ n ∈ R,0 < n)
    (u v : ℕ → ℂ) (θ Y t : ℝ) (hY : 0 < Y) :
    (∑ p ∈ S,∑ n ∈ R,
      (η ((p*n:ℕ)/Y)*Complex.exp (-(2*(Real.pi:ℂ)*Complex.I*(θ:ℂ)*(((p*n:ℕ):ℝ)/Y:ℝ))))*
        (u p*v n)*markedPrimePhase (p*n) t) =
      ∫ ξ : ℝ,markedMellinIsolationCoefficient η hη ha hsupp θ ξ *
        Complex.exp (-(Complex.I*(ξ:ℂ)*(Real.log Y:ℂ)))*
        (∑ p ∈ S,u p*markedPrimePhase p (t+ξ))*(∑ n ∈ R,v n*markedPrimePhase n (t+ξ)) := by
  classical
  let F := fun ξ => markedMellinIsolationCoefficient η hη ha hsupp θ ξ
  let g := fun p n ξ => F ξ*Complex.exp (Complex.I*(ξ:ℂ)*(Real.log ((p*n:ℕ)/Y):ℂ))*
    (u p*v n)*markedPrimePhase (p*n) t
  have hg : ∀ p n,Integrable (g p n) := by
    intro p n
    exact ((markedMellinIsolation_phase_integrable η hη ha hsupp θ
      (Real.log ((p*n:ℕ)/Y))).mul_const (u p*v n)).mul_const (markedPrimePhase (p*n) t)
  calc
    _ = ∑ p ∈ S,∑ n ∈ R,∫ ξ : ℝ,g p n ξ := by
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro n hn
      rw [markedMellinIsolation_inversion η hη ha hsupp θ
        (div_pos (by exact_mod_cast Nat.mul_pos (hS p hp) (hR n hn)) hY)]
      simp only [g,F,integral_mul_const]
    _ = ∫ ξ : ℝ,∑ p ∈ S,∑ n ∈ R,g p n ξ := by
      rw [integral_finsetSum _ (fun p _ => integrable_finsetSum R (fun n _ => hg p n))]
      apply sum_congr rfl
      intro p _
      exact (integral_finsetSum R (fun n _ => hg p n)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [mul_sum,sum_mul]
      rw [sum_comm (s := R) (t := S)]
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro n hn
      have he := markedMajorLabel_mellin_phase (hS p hp) (hR n hn) hY t ξ
      dsimp [g,F]
      calc
        _ = (u p*v n)*markedMellinIsolationCoefficient η hη ha hsupp θ ξ*
          (Complex.exp (Complex.I*(ξ:ℂ)*(Real.log ((p*n:ℕ)/Y):ℂ))*markedPrimePhase (p*n) t) := by ring
        _ = _ := by rw [he]; ring

end ArtinMatthews
