module

public import ArtinMatthews.HeckeCubicPrimeSmooth
public import ArtinMatthews.PrimeExtractionLogMomentDecay


set_option backward.privateInPublic true
@[expose] public section

/-! The actual smooth prime remainder saves every logarithmic power for
each fixed Dirichlet character. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths Filter
open scoped ContDiff Topology Asymptotics

theorem cubicNumeratorPrimeSmooth_isLittleO (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (D : ℝ) :
    (fun x : ℝ => heckeRationalPrimeSmoothSum (cubicNumeratorHeckeCharacter A hA) χ W x 0)
      =o[atTop] (fun x : ℝ => x*(Real.log x)^(-D)) := by
  apply prime_extraction_all_log_moments_isLittleO
  intro k
  refine ⟨1, ?_⟩
  filter_upwards [cubicNumeratorPrimeSmooth_all_log A hA hnoncube W a b ha hsupp hW
    1 0 1 ((k : ℝ)-2) (by norm_num) (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (q : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x hbound hq hx
  have hb := hbound q (by simpa only [Real.rpow_one] using hq) χ x
    (by simp only [Real.rpow_one, le_refl]) 0 (by simp)
  convert hb using 1
  rw [show -((k : ℝ)-2) = 2-(k : ℝ) by ring,
    Real.rpow_sub (Real.log_pos hx), Real.rpow_two, Real.rpow_natCast]
  ring

end ArtinMatthews
