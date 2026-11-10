module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- The log of the squared complex radius carries `2 dr/r` to Lebesgue measure. -/
theorem sourceLogRadial_lintegral (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioi 0, ENNReal.ofReal (2 / r) * f r) =
      ∫⁻ t : ℝ, f (Real.exp (t / 2)) := by
  let e : ℝ → ℝ := fun t => Real.exp (t / 2)
  have hd (t : ℝ) : HasDerivWithinAt e (e t / 2) univ t := by
    have h := (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
    simpa only [e, Function.comp_def, id_eq, mul_one_div] using h.hasDerivWithinAt (s := univ)
  have he : Function.Injective e := fun a b h => by
    have h' : a / 2 = b / 2 := Real.exp_injective h
    linarith
  have hi : e '' univ = Ioi 0 := by
    ext r
    constructor
    · rintro ⟨t, _, rfl⟩
      exact Real.exp_pos _
    · intro hr
      exact ⟨2 * Real.log r, mem_univ _, by
        change Real.exp (2 * Real.log r / 2) = r
        rw [show 2 * Real.log r / 2 = Real.log r by ring, Real.exp_log hr]⟩
  rw [← hi, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun t _ => hd t) he.injOn, Measure.restrict_univ]
  apply lintegral_congr
  intro t
  have ht : 0 < e t := Real.exp_pos _
  rw [abs_of_pos (by positivity : 0 < e t / 2), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  rw [show e t / 2 * (2 / e t) = 1 by field_simp, ENNReal.ofReal_one, one_mul]

end
end ArtinMatthews.SourcePhysical
