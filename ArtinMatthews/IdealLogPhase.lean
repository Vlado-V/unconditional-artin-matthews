module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Circle


set_option backward.privateInPublic true
@[expose] public section

/-! The original Mellin and additive factors as one phase in the real
logarithmic variable, with its exact frequency dependence. -/
namespace ArtinMatthews
noncomputable section

def idealLogPhase (ζ β v : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((ζ*v + 2*Real.pi*β*Real.exp v : ℝ) : ℂ))

theorem idealLogPhase_eq (ζ β v : ℝ) :
    idealLogPhase ζ β v =
      (Real.exp v : ℂ)^(Complex.I*(ζ : ℂ)) * (Real.fourierChar (β*Real.exp v) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp, Real.fourierChar_apply,
    ← Complex.exp_add]
  unfold idealLogPhase
  congr 1
  push_cast
  ring_nf

theorem idealLogPhase_norm (ζ β v : ℝ) : ‖idealLogPhase ζ β v‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

theorem idealImaginaryExp_sub_le (s t : ℝ) :
    ‖Complex.exp (Complex.I*(s : ℂ)) - Complex.exp (Complex.I*(t : ℂ))‖ ≤ |s-t| := by
  have he : Complex.exp (Complex.I*(s : ℂ)) - Complex.exp (Complex.I*(t : ℂ)) =
      Complex.exp (Complex.I*(t : ℂ)) *
        (Complex.exp (Complex.I*((s-t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s-t))

theorem idealExp_sub_le {M v w : ℝ} (hM : 0 < M)
    (hv : v ≤ Real.log M) (hw : w ≤ Real.log M) :
    |Real.exp v - Real.exp w| ≤ M * |v-w| := by
  have hd (x : ℝ) (hx : x ∈ Set.Iic (Real.log M)) : ‖Real.exp x‖ ≤ M := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_exp.mpr hx).trans_eq (Real.exp_log hM)
  have hh := (convex_Iic (Real.log M)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) hd hw hv
  simpa only [Real.norm_eq_abs] using hh

theorem idealLogPhase_sub_le (ζ β : ℝ) {M v w : ℝ} (hM : 0 < M)
    (hv : v ≤ Real.log M) (hw : w ≤ Real.log M) :
    ‖idealLogPhase ζ β v - idealLogPhase ζ β w‖ ≤
      (|ζ| + 2*Real.pi * |β| * M) * |v-w| := by
  apply (idealImaginaryExp_sub_le _ _).trans
  have hexp := idealExp_sub_le hM hv hw
  have he : ζ*v + 2*Real.pi*β*Real.exp v - (ζ*w + 2*Real.pi*β*Real.exp w) =
      ζ*(v-w) + 2*Real.pi*β*(Real.exp v-Real.exp w) := by ring_nf
  rw [he]
  calc
    _ ≤ |ζ*(v-w)| + |2*Real.pi*β*(Real.exp v-Real.exp w)| := abs_add_le _ _
    _ = |ζ| * |v-w| + (2*Real.pi * |β|) * |Real.exp v-Real.exp w| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
    _ ≤ |ζ| * |v-w| + (2*Real.pi * |β|)*(M * |v-w|) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp (by positivity))
    _ = _ := by ring_nf

end
end ArtinMatthews
