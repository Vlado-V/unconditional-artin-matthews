module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import ArtinMatthews.SpectralJForwardTransform
public import Mathlib.Analysis.Complex.RemovableSingularity


set_option backward.privateInPublic true
@[expose] public section

/-! The exact even divided-order quotient is holomorphic through zero.
The denominator has no other zero in the open unit strip. -/
noncomputable section
open Set Complex
open scoped Topology

namespace ArtinMatthews

theorem spectralJDividedOrder_differentiableOn (A : ℂ → ℂ)
    (hA : Differentiable ℂ A) :
    DifferentiableOn ℂ (fun z => if z = 0 then -(2/(Real.pi : ℂ))*deriv A 0
      else (A (-2*I*z)-A (2*I*z))/(2*Complex.sin ((Real.pi : ℂ)*I*z)))
      {z : ℂ | |z.im| < 1} := by
  let s : Set ℂ := {z : ℂ | |z.im| < 1}
  let N (z : ℂ) := A (-2*I*z)-A (2*I*z)
  let S (z : ℂ) := 2*Complex.sin ((Real.pi : ℂ)*I*z)
  have hs : s ∈ 𝓝 (0 : ℂ) :=
    (isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds (by simp)
  have hN : Differentiable ℂ N := (hA.comp (by fun_prop)).sub (hA.comp (by fun_prop))
  have hS : Differentiable ℂ S := by dsimp only [S]; fun_prop
  have hNzero : N 0 = 0 := by simp [N]
  have hSzero : S 0 = 0 := by simp [S]
  have hMinus : HasDerivAt (fun z => A (-2*I*z)) (deriv A 0*(-2*I)) 0 := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hA 0).hasDerivAt.comp_of_eq (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_mul (-2*I)) (by simp)
  have hPlus : HasDerivAt (fun z => A (2*I*z)) (deriv A 0*(2*I)) 0 := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hA 0).hasDerivAt.comp_of_eq (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).const_mul (2*I)) (by simp)
  have hN' : HasDerivAt N ((-4*I)*deriv A 0) 0 := by
    convert hMinus.sub hPlus using 1
    ring
  have hS' : HasDerivAt S (2*(Real.pi : ℂ)*I) 0 := by
    have h := ((Complex.hasDerivAt_sin (0 : ℂ)).comp_of_eq (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).const_mul ((Real.pi : ℂ)*I)) (by simp)).const_mul 2
    simpa only [S, Function.comp_def, id_eq, mul_one, Complex.cos_zero, one_mul, mul_assoc] using h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hSN (z : ℂ) (hz : z ∈ s) : dslope S 0 z ≠ 0 := by
    by_cases h : z = 0
    · subst z
      rw [dslope_same, hS'.deriv]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hπ) I_ne_zero
    · simp only [dslope_of_ne S h, slope_def_field, hSzero, sub_zero]
      exact div_ne_zero (spectralJForwardKernel_denominator_ne_zero h hz) h
  have hDN := (Complex.differentiableOn_dslope hs).mpr hN.differentiableOn
  have hDS := (Complex.differentiableOn_dslope hs).mpr hS.differentiableOn
  apply (hDN.div hDS hSN).congr
  intro z hz
  change (if z = 0 then -(2/(Real.pi : ℂ))*deriv A 0 else N z/S z) =
    dslope N 0 z/dslope S 0 z
  by_cases h : z = 0
  · subst z
    rw [ite_eq_left rfl, dslope_same, dslope_same, hN'.deriv, hS'.deriv]
    field_simp [hπ, I_ne_zero] <;> ring
  · simp only [ite_eq_right h, dslope_of_ne N h, dslope_of_ne S h, slope_def_field,
      hNzero, hSzero, sub_zero]
    change N z/S z = (N z/z)/(S z/z)
    exact (div_div_div_cancel_right₀ h (N z) (S z)).symm

end ArtinMatthews
