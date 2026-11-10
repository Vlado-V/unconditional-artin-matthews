module

public import ArtinMatthews.SourceContourHeightWeight
public import OAI.NumberTheory.DirichletL.Detector.Physical
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.PrincipalMellinResidues


set_option backward.privateInPublic true
@[expose] public section

/-! A one-pole shift with the horizontal limits proved from the integrable height weight. -/

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Filter Set Complex
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.PrincipalMellinResidues
open scoped Topology
noncomputable section

theorem source_verticalIntegral_simple_pole_of_heightWeight (A F : ℂ → ℂ) {a b p C : ℝ}
    (hap : a < p) (hpb : p < b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ (p : ℂ) → F z = A z / (z - p))
    (hleft : ∀ t : ℝ, ‖F ((a : ℂ) + t * I)‖ ≤ C * sourceContourHeightWeight t)
    (hright : ∀ t : ℝ, ‖F ((b : ℂ) + t * I)‖ ≤ C * sourceContourHeightWeight t)
    (hside : ∀ x ∈ Icc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖F ((x : ℂ) + t * I)‖ ≤ C * sourceContourHeightWeight t) :
    verticalIntegral b F = verticalIntegral a F + A p := by
  have hab := hap.le.trans hpb.le
  have hV (x : ℝ) (hx : x ∈ Icc a b) (hp : x ≠ p)
      (hbound : ∀ t : ℝ, ‖F ((x : ℂ) + t * I)‖ ≤ C * sourceContourHeightWeight t) :
      Integrable (fun t : ℝ => F ((x : ℂ) + t * I)) := by
    let L (t : ℝ) := (x : ℂ) + t * I
    have hc : Continuous L := by unfold L; fun_prop
    have hL (t : ℝ) : (L t).re = x := by simp [L, Complex.mul_re]
    have hn (t : ℝ) : L t ≠ (p : ℂ) := by
      intro h
      exact hp (by simpa only [hL, Complex.ofReal_re] using congrArg Complex.re h)
    have hEq : (fun t : ℝ => F (L t)) = (fun t : ℝ => A (L t) / (L t - p)) :=
      funext fun t => hF _ (by rw [hL]; exact hx.1) (by rw [hL]; exact hx.2) (hn t)
    have hcont : Continuous (fun t : ℝ => F (L t)) := by
      rw [hEq]
      exact (hA.continuousOn.comp_continuous hc (fun t => by simpa only [mem_ofPred_eq, hL, mem_Icc] using hx)).div
        (hc.sub continuous_const) (fun t => sub_ne_zero.mpr (hn t))
    exact (sourceContourHeightWeight_integrable.const_mul C).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hbound)
  have hH (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
      Tendsto (fun T : ℝ => ∫ x in a..b, F ((x : ℂ) + (ε * T : ℝ) * I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using (sourceContourHeightWeight_tendsto.const_mul C).mul_const |b - a|)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hx
    rcases hε with rfl | rfl
    · simpa only [one_mul] using hside x hx' T (hT.trans (le_abs_self T))
    · simpa only [neg_one_mul, sourceContourHeightWeight_neg] using
        hside x hx' (-T) (by rw [abs_neg]; exact hT.trans (le_abs_self T))
  exact verticalIntegral_simple_pole A F hap hpb hA hF
    (hV a ⟨le_rfl, hab⟩ hap.ne hleft) (hV b ⟨hab, le_rfl⟩ hpb.ne' hright)
    (by simpa only [neg_one_mul, Complex.ofReal_neg] using hH (-1) (Or.inr rfl))
    (by simpa only [one_mul] using hH 1 (Or.inl rfl))

end
end ArtinMatthews.SourcePhysical
