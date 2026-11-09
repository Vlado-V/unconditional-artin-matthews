module

public import ArtinMatthews.SpectralGamma0EisensteinPlaneTerms
public import ArtinMatthews.SpectralEisensteinPowerBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine compact row majorants for the first two spatial derivatives, still for Re(s)>1. -/
noncomputable section
open Set
namespace ArtinMatthews

def gamma0EisensteinRowMajorant (N : ℕ) (s : ℂ) (A a b : ℝ) (ha : 0<a)
    (v : Gamma0EisensteinRows N) : ℝ :=
  (b^s.re*(EisensteinSeries.r ⟨⟨A,a⟩,ha⟩)^(-(2*s.re)))*‖v.val‖^(-(2*s.re))

theorem gamma0EisensteinRowMajorant_summable (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) : Summable (gamma0EisensteinRowMajorant N s A a b ha) :=
  ((EisensteinSeries.summable_one_div_norm_rpow (show 2<2*s.re by linarith)).subtype
    (fun v => v ∈ Set.range (gamma0EisensteinRow N))).mul_left _

theorem gamma0EisensteinPlaneTerm_majorant (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) (hab : a≤b) (v : Gamma0EisensteinRows N)
    (p : ℝ × ℝ) (hp : |p.1|≤A ∧ a≤p.2 ∧ p.2≤b) :
    ‖gamma0EisensteinPlaneTerm N s v p‖ ≤ gamma0EisensteinRowMajorant N s A a b ha v := by
  have hpy : 0<p.2 := ha.trans_le hp.2.1
  let z : UpperHalfPlane := ⟨⟨p.1,p.2⟩,hpy⟩
  have hz : z ∈ UpperHalfPlane.verticalStrip A a := ⟨hp.1,hp.2.1⟩
  rw [gamma0EisensteinPlaneTerm_eq N s v p hpy,gamma0EisensteinSummand_norm_row]
  have hd := EisensteinSeries.summand_bound_of_mem_verticalStrip
    (show 0≤2*s.re by linarith) v.val ha hz
  have hy : p.2^s.re ≤ b^s.re := Real.rpow_le_rpow hpy.le hp.2.2 (by linarith)
  exact (mul_le_mul hy hd (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (ha.trans_le hab).le _)).trans_eq
    (mul_assoc _ _ _).symm

theorem gamma0EisensteinPlaneTerm_derivative_majorants (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) (hab : a≤b) (v : Gamma0EisensteinRows N)
    (p : ℝ × ℝ) (hp : |p.1|≤A ∧ a≤p.2 ∧ p.2≤b) :
    ‖fderiv ℝ (gamma0EisensteinPlaneTerm N s v) p‖ ≤
        (5*‖s‖/a)*gamma0EisensteinRowMajorant N s A a b ha v ∧
    ‖fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneTerm N s v)) p‖ ≤
        ((50*‖s‖^2+42*‖s‖)/a^2)*gamma0EisensteinRowMajorant N s A a b ha v := by
  have hpy : 0<p.2 := ha.trans_le hp.2.1
  have hf := gamma0EisensteinPlaneTerm_majorant N s hs A a b ha hab v p hp
  have hcd := gamma0EisensteinRow_coefficients_ne_zero N v
  have h1 := eisensteinRowPower_fderiv_bound s (v.val 0) (v.val 1) hcd p hpy
  have h2 := eisensteinRowPower_second_bound s (v.val 0) (v.val 1) hcd p hpy
  have hden1 : 5*‖s‖/p.2 ≤ 5*‖s‖/a := div_le_div_of_nonneg_left (by positivity) ha hp.2.1
  have hden2 : (50*‖s‖^2+42*‖s‖)/p.2^2 ≤ (50*‖s‖^2+42*‖s‖)/a^2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha) (pow_le_pow_left₀ ha.le hp.2.1 2)
  constructor
  · exact h1.trans (mul_le_mul hden1 hf (norm_nonneg _) (by positivity))
  · exact h2.trans (mul_le_mul hden2 hf (norm_nonneg _) (by positivity))

end ArtinMatthews
