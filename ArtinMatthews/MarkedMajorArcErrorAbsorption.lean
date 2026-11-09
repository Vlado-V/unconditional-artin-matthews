module

public import ArtinMatthews.MarkedMajorArcErrorAbsorptionAssemble
public import ArtinMatthews.MarkedMajorArcErrorAbsorptionBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary logarithmic savings for the actual sharp-interval error. -/
namespace ArtinMatthews
open Filter
open scoped Topology

theorem marked_major_interval_uniform_power (K C η τ A D B c : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hη : 0 < η) (hτ : 0 < τ) (hA : 0 ≤ A)
    (hD : A+3 < D) (hB : A+D+5 < B) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ u v : ℝ,
      Real.exp (τ*L) ≤ u → u ≤ v → v ≤ 2*u → v ≤ Real.exp (η*L) →
      markedMajorIntervalError K C L (L^B) (L^(-D)) u v ≤ c*L^(-A) := by
  have hD0 : 0 ≤ D := by linarith
  have hR := marked_major_riesz_uniform_power K C (η+1) τ (A+D) B (c/12)
    hK hC hτ (by linarith) hB (by positivity)
  have hBd := marked_major_boundary_uniform_power A η τ D (c/2)
    hA hτ hη hD (by positivity)
  filter_upwards [hR,hBd,eventually_ge_atTop (1 : ℝ)] with L hR hBd hL u v hlo huv hv2 hhi
  have hLp : 0 < L := by linarith
  have hE : 0 ≤ L^(-D) := Real.rpow_nonneg hLp.le _
  have hupper : Real.exp (η*L) ≤ Real.exp ((η+1)*L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hplain (x : ℝ) (hxlo : Real.exp (τ*L) ≤ x)
      (hxhi : x ≤ Real.exp (η*L)) :
      markedMajorRieszError K C L (L^B) x ≤ (c/12)*L^(-(A+D)) :=
    hR x hxlo (hxhi.trans hupper)
  have hscaled (x : ℝ) (hxlo : Real.exp (τ*L) ≤ x)
      (hxhi : x ≤ Real.exp (η*L)) :
      markedMajorRieszError K C L (L^B) ((1+L^(-D))*x) ≤ (c/12)*L^(-(A+D)) := by
    have hx : 0 ≤ x := (Real.exp_pos _).le.trans hxlo
    apply hR
    · exact hxlo.trans (by nlinarith [mul_nonneg hE hx])
    · exact marked_major_smoothed_upper hL hD0 hx hxhi
  exact marked_major_interval_error_power_of_four hL hc.le hD0
    (hscaled v (hlo.trans huv) hhi) (hscaled u hlo (huv.trans hhi))
    (hplain v (hlo.trans huv) hhi) (hplain u hlo (huv.trans hhi))
    (hBd u v hlo huv hv2 hhi)

end ArtinMatthews
