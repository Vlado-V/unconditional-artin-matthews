module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/- Adapted from OpenAI Math, Apache-2.0. The moving-strip helpers are retained with the independent real-pole input. -/
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogGrowth
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrincipalCorrection
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterPositivity
public import ArtinMatthews.IndependentZetaPole


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Principal-character comparison and the arithmetic step of the moving
character strip. These are the retained helpers from the fixed-height file. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

lemma mrt_character_principal_neg_logderiv_re {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s).re ≤
        (-deriv riemannZeta s / riemannZeta s).re + Real.log (q : ℝ) := by
  have h := (Complex.abs_re_le_norm _).trans (mrt_principal_logderiv_error (q := q) hs)
  rw [Complex.sub_re] at h
  have := (abs_le.mp h).1
  simp only [logDeriv_apply] at this
  simp only [neg_div, Complex.neg_re]
  linarith

lemma mrt_character_zero_free_arithmetic {D H delta eps : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hd : delta = 1 / (10 * D * H))
    (he : 0 ≤ eps) (heu : eps ≤ delta / 4) :
    3 / delta + D * H - 4 / (delta + eps) < 0 := by
  have hdp : 0 < delta := by rw [hd]; positivity
  have hde : 0 < delta + eps := by linarith
  have hinv : 16 / (5 * delta) ≤ 4 / (delta + eps) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 5 * delta) hde).mpr
    nlinarith
  have heq : 3 / delta + D * H - 16 / (5 * delta) = -(D * H) := by
    rw [hd]
    field_simp [hD.ne', hH.ne']
    ring
  have hle : 3 / delta + D * H - 4 / (delta + eps) ≤
      3 / delta + D * H - 16 / (5 * delta) := by linarith
  rw [heq] at hle
  exact hle.trans_lt (neg_neg_of_pos (mul_pos hD hH))

end TwoPointCorrelations

end OAI
