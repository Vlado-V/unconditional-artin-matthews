module

public import ArtinMatthews.SpectralEisensteinPowerCalculus
public import ArtinMatthews.SpectralGamma0EisensteinSeries
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

/-! The differentiated plane functions are the actual convergent Eisenstein summands. -/
noncomputable section
open Set
open scoped ContDiff MatrixGroups
namespace ArtinMatthews

theorem eisensteinRowQuadratic_norm_sq (c d : ℝ) (p : ℝ × ℝ) :
    eisensteinRowQuadratic c d p = ‖(c:ℂ)*Complex.mk p.1 p.2+d‖^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [eisensteinRowQuadratic,Complex.normSq_apply,pow_two]

theorem eisensteinRowPower_eq_height (s : ℂ) (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    eisensteinRowPower s c d p = ((p.2/eisensteinRowQuadratic c d p : ℝ):ℂ)^s := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  have hh : 0 < p.2/eisensteinRowQuadratic c d p := div_pos hp hq
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne'),
    ← Complex.ofReal_log hh.le,Real.log_div hp.ne' hq.ne']
  unfold eisensteinRowPower eisensteinRowLog
  push_cast
  congr 1
  ring

theorem gamma0EisensteinRow_coefficients_ne_zero (N : ℕ) (v : Gamma0EisensteinRows N) :
    (v.val 0 : ℝ) ≠ 0 ∨ (v.val 1 : ℝ) ≠ 0 := by
  by_cases hc : (v.val 0 : ℝ) = 0
  · right
    intro hd
    apply gamma0EisensteinRows_ne_zero N v
    funext i
    fin_cases i
    · exact_mod_cast hc
    · exact_mod_cast hd
  · exact Or.inl hc

def gamma0EisensteinPlaneTerm (N : ℕ) (s : ℂ) (v : Gamma0EisensteinRows N) (p : ℝ × ℝ) : ℂ :=
  eisensteinRowPower s (v.val 0) (v.val 1) p

theorem gamma0EisensteinPlaneTerm_eq (N : ℕ) (s : ℂ) (v : Gamma0EisensteinRows N)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    gamma0EisensteinPlaneTerm N s v p = gamma0EisensteinSummand N s v ⟨Complex.mk p.1 p.2,hp⟩ := by
  have hq : eisensteinRowQuadratic (v.val 0) (v.val 1) p =
      ‖(v.val 0 : ℂ)*Complex.mk p.1 p.2+v.val 1‖^2 := by
    simpa only [Complex.ofReal_intCast] using
      eisensteinRowQuadratic_norm_sq (v.val 0) (v.val 1) p
  rw [gamma0EisensteinPlaneTerm,eisensteinRowPower_eq_height s _ _
    (gamma0EisensteinRow_coefficients_ne_zero N v) p hp,gamma0EisensteinSummand,
    gamma0EisensteinHeight_row,hq]
  rfl

theorem gamma0EisensteinPlaneTerm_contDiffOn (N : ℕ) (s : ℂ) (v : Gamma0EisensteinRows N) :
    ContDiffOn ℝ ∞ (gamma0EisensteinPlaneTerm N s v) {p : ℝ × ℝ | 0 < p.2} :=
  eisensteinRowPower_contDiffOn s _ _ (gamma0EisensteinRow_coefficients_ne_zero N v)

def gamma0EisensteinPlaneSum (N : ℕ) (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (1/2:ℂ)*∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v p

theorem gamma0EisensteinPlaneSum_eq (N : ℕ) (s : ℂ) (p : ℝ × ℝ) (hp : 0 < p.2) :
    gamma0EisensteinPlaneSum N s p = gamma0Eisenstein N s ⟨Complex.mk p.1 p.2,hp⟩ := by
  unfold gamma0EisensteinPlaneSum gamma0Eisenstein
  congr 1
  exact tsum_congr (fun v => gamma0EisensteinPlaneTerm_eq N s v p hp)

end ArtinMatthews
