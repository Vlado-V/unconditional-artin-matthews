module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Complex.PhragmenLindelof


set_option backward.privateInPublic true
@[expose] public section

/-! The strip maximum principle with an explicit quadratic-growth input.
This analytic helper does not assume the boundary estimates that will be
derived from the actual primitive functional equation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Complex Filter Asymptotics Set
open scoped Topology
noncomputable section

theorem eventually_quadratic_le_exp {c D : ℝ} (hc : 0 < c) (hD : 0 ≤ D) :
    ∀ᶠ T : ℝ in atTop, D*(T+2)^2 ≤ Real.exp (c*T) := by
  have ht : Tendsto (fun T : ℝ => Real.exp (c*T)/T^2) atTop atTop := by
    simpa using tendsto_exp_mul_div_rpow_atTop 2 c hc
  filter_upwards [ht.eventually_ge_atTop (9*D),eventually_ge_atTop (1 : ℝ)] with T hT hT1
  have hlarge := (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < T))).mp hT
  have hsq : (T+2)^2 ≤ 9*T^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hsq hD).trans (by nlinarith)

theorem norm_le_on_vertical_strip_of_quadratic_growth
    {f : ℂ → ℂ} {a b C A D R : ℝ} (hab : a < b) (hA : 0 < A) (hD : 0 ≤ D)
    (hfd : DiffContOnCl ℂ f (Complex.re ⁻¹' Ioo a b))
    (hgrowth : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → R ≤ |z.im| →
      ‖f z‖ ≤ A*Real.exp (D*(|z.im|+2)^2))
    (ha : ∀ z : ℂ, z.re=a → ‖f z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re=b → ‖f z‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : ‖f z‖ ≤ C := by
  apply PhragmenLindelof.vertical_strip hfd _ ha hb hza hzb
  let c : ℝ := Real.pi/(2*(b-a))
  have hc : 0 < c := div_pos Real.pi_pos (by linarith)
  have hclt : c < Real.pi/(b-a) := by
    dsimp [c]
    have hd : 0 < b-a := sub_pos.mpr hab
    field_simp
    nlinarith [Real.pi_pos]
  refine ⟨c,hclt,1,?_⟩
  apply IsBigO.of_bound A
  rw [Filter.eventually_inf_principal]
  have H := ((eventually_ge_atTop R).and (eventually_quadratic_le_exp hc hD)).comap
    (fun w : ℂ => |w.im|)
  filter_upwards [H] with w hw hstrip
  have h := hgrowth w hstrip.1.le hstrip.2.le hw.1
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul]
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw.2) hA.le)

end
end ArtinMatthews.VaryingKummerAnalytic
