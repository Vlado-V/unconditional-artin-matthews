module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold


set_option backward.privateInPublic true
@[expose] public section

/-! Actual two-dimensional conformal transport of Dirichlet energy.
The Möbius derivative is reused directly from Mathlib's upper-half-plane
manifold; no transformation law is assumed. -/

noncomputable section
open scoped MatrixGroups

namespace ArtinMatthews

/-- The sum of the two actual real coordinate derivative squares. -/
def h2TangentEnergy (A : ℂ →L[ℝ] ℂ) : ℝ := ‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2

/-- Multiplication by a complex scalar scales the real Hilbert-Schmidt energy
by its norm square, for arbitrary real-linear complex-valued differentials. -/
theorem h2TangentEnergy_complex_mul (A : ℂ →L[ℝ] ℂ) (c : ℂ) :
    ‖A c‖ ^ 2 + ‖A (c * Complex.I)‖ ^ 2 = ‖c‖ ^ 2 * h2TangentEnergy A := by
  have hc : c = c.re • (1 : ℂ) + c.im • Complex.I := by
    apply Complex.ext <;> simp
  have hci : c * Complex.I = (-c.im) • (1 : ℂ) + c.re • Complex.I := by
    apply Complex.ext <;> simp
  have hAc : A c = c.re • A 1 + c.im • A Complex.I := by
    conv_lhs => rw [hc]
    rw [map_add, map_smul, map_smul]
  have hAci : A (c * Complex.I) = (-c.im) • A 1 + c.re • A Complex.I := by
    rw [hci, map_add, map_smul, map_smul]
  rw [hAc, hAci]
  simp only [h2TangentEnergy, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- The energy in complex coordinates uses actual real Fréchet derivatives. -/
def h2FunctionEnergy (f : ℂ → ℂ) (z : ℂ) : ℝ := h2TangentEnergy (fderiv ℝ f z)

theorem h2_smulFDeriv_apply (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    (z v : ℂ) :
    UpperHalfPlane.smulFDeriv g z v = (g.det.val / UpperHalfPlane.denom g z ^ 2 : ℂ) * v := by
  change 0 < g.val.det at hg
  simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, hg, mul_comm]

/-- The exact derivative scale agrees with the height ratio. -/
theorem h2_smul_derivative_norm (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    (z : UpperHalfPlane) :
    ‖(g.det.val / UpperHalfPlane.denom g z ^ 2 : ℂ)‖ = (g • z).im / z.im := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hg.le,
    UpperHalfPlane.im_smul_eq_div_normSq, abs_of_pos hg, Complex.normSq_eq_norm_sq]
  field_simp

/-- Actual H² Dirichlet energy is invariant under orientation-preserving
Möbius pullback, with differentiability the only premise on the test function. -/
theorem h2FunctionEnergy_mobius (f : ℂ → ℂ) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) (z : UpperHalfPlane)
    (hf : DifferentiableAt ℝ f (g • z : UpperHalfPlane)) :
    z.im ^ 2 * h2FunctionEnergy
        (fun w : ℂ => f (g • UpperHalfPlane.ofComplex w : UpperHalfPlane)) z =
      (g • z).im ^ 2 * h2FunctionEnergy f (g • z : UpperHalfPlane) := by
  let m : ℂ → ℂ := fun w => (g • UpperHalfPlane.ofComplex w : UpperHalfPlane)
  have hm := (UpperHalfPlane.hasStrictFDerivAt_smul g z).hasFDerivAt
  have hcomp : fderiv ℝ (f ∘ m) z = (fderiv ℝ f (g • z : UpperHalfPlane)).comp
      (UpperHalfPlane.smulFDeriv g z) := by
    have hf' : DifferentiableAt ℝ f (m (z : ℂ)) := by
      simpa only [m, UpperHalfPlane.ofComplex_apply] using hf
    simpa only [m, UpperHalfPlane.ofComplex_apply] using
      (hf'.hasFDerivAt.comp (z : ℂ) hm).fderiv
  change z.im ^ 2 * h2TangentEnergy (fderiv ℝ (f ∘ m) z) = _
  rw [hcomp]
  have he : h2TangentEnergy ((fderiv ℝ f (g • z : UpperHalfPlane)).comp
      (UpperHalfPlane.smulFDeriv g z)) =
      ‖(g.det.val / UpperHalfPlane.denom g z ^ 2 : ℂ)‖ ^ 2 *
        h2FunctionEnergy f (g • z : UpperHalfPlane) := by
    unfold h2TangentEnergy
    simp only [ContinuousLinearMap.comp_apply, h2_smulFDeriv_apply g hg, mul_one]
    exact h2TangentEnergy_complex_mul _ _
  rw [he, h2_smul_derivative_norm g hg z]
  field_simp

end ArtinMatthews
