module

public import Mathlib.NumberTheory.Modular
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import ArtinMatthews.SpectralHyperbolicL2
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


set_option backward.privateInPublic true
@[expose] public section

/-! Finite invariant area of the actual modular fundamental region. -/

noncomputable section
open MeasureTheory Set

namespace ArtinMatthews

/-- Restricted coordinate integrability for the actual invariant measure. -/
theorem upperHalfPlane_integrableOn_coordinates (G : ℝ × ℝ → ℝ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    IntegrableOn (fun z : UpperHalfPlane => G (z.re, z.im))
      {z | (z.re, z.im) ∈ S} ↔
      IntegrableOn (fun p => G p / p.2 ^ 2) S := by
  classical
  have h := upperHalfPlane_integrable_coordinates (S.indicator G)
  have hleft : (fun z : UpperHalfPlane => S.indicator G (z.re, z.im)) =
      {z : UpperHalfPlane | (z.re, z.im) ∈ S}.indicator
        (fun z => G (z.re, z.im)) := rfl
  have hright : (fun p : ℝ × ℝ => S.indicator G p / p.2 ^ 2) =
      S.indicator (fun p => G p / p.2 ^ 2) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re, z.im) ∈ S} :=
    hS.preimage (by fun_prop)
  rw [hleft, integrable_indicator_iff hpre, hright] at h
  change _ ↔ Integrable _ (volume.restrict _) at h
  rw [integrable_indicator_iff hS] at h
  change _ ↔ Integrable _ ((volume.restrict {p : ℝ × ℝ | 0 < p.2}).restrict S) at h
  rw [Measure.restrict_restrict_of_subset hpositive] at h
  exact h

/-- Every bounded horizontal strip above positive height has finite H² area. -/
theorem hyperbolic_strip_volume_lt_top (a b Y : ℝ) (hY : 0 < Y) :
    (volume : Measure UpperHalfPlane) {z | z.re ∈ Icc a b ∧ Y < z.im} < ⊤ := by
  have hy : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ioi Y) := by
    have hr := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hY
    apply hr.congr_fun _ measurableSet_Ioi
    intro y hy
    change Real.rpow y (-(2 : ℝ)) = 1 / y ^ 2
    calc
      _ = (y ^ (2 : ℝ))⁻¹ := Real.rpow_neg (le_of_lt (hY.trans hy)) 2
      _ = _ := by rw [Real.rpow_two, one_div]
  have hx : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc a b)) :=
    integrable_const 1
  have hprod := hx.mul_prod hy
  have hplane : IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) / p.2 ^ 2)
      ((Icc a b) ×ˢ (Ioi Y)) := by
    change Integrable _ ((volume.prod volume).restrict _)
    rw [← Measure.prod_restrict]
    simpa only [one_mul] using hprod
  have hhalf := (upperHalfPlane_integrableOn_coordinates (fun _ => (1 : ℝ))
    (measurableSet_Icc.prod measurableSet_Ioi) (fun p hp => hY.trans hp.2)).mpr hplane
  change IntegrableOn (fun _ : UpperHalfPlane => (1 : ℝ))
    {z | z.re ∈ Icc a b ∧ Y < z.im} volume at hhalf
  simpa using hhalf

/-- Finite area is derived from the actual defining inequalities of the
standard modular fundamental region, without assuming a quotient measure. -/
theorem modular_fundamental_region_volume_lt_top :
    (volume : Measure UpperHalfPlane) ModularGroup.fd < ⊤ := by
  apply lt_of_le_of_lt (measure_mono ?_)
    (hyperbolic_strip_volume_lt_top (-(1 : ℝ) / 2) (1 / 2) (1 / 2) (by norm_num))
  intro z hz
  refine ⟨?_, ?_⟩
  · change -(1 : ℝ) / 2 ≤ z.re ∧ z.re ≤ 1 / 2
    constructor <;> linarith [(abs_le.mp hz.2).1, (abs_le.mp hz.2).2]
  · have hs := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
    nlinarith [z.im_pos]

end ArtinMatthews
