module

public import ArtinMatthews.SourceHilbertPencilParameter
public import Mathlib.Analysis.Meromorphic.Basic
public import ArtinMatthews.SourceHilbertMeromorphicResolvent
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Eisenstein.MeromorphicResolvent


set_option backward.privateInPublic true
@[expose] public section

/-! The source spectral parameter takes the right half-plane into the
nonreal region or the real Fredholm region. In its initial half-plane
the inverse is analytic by the Gram coercivity bound. -/

namespace ArtinMatthews.HilbertResolvent

open scoped InnerProductSpace Topology
noncomputable section

def spectralParameter (r : ℝ) (s : ℂ) : ℂ := (r : ℂ) * (1 - 4 * s ^ 2)

theorem spectralParameter_analyticAt (r : ℝ) (s : ℂ) : AnalyticAt ℂ (spectralParameter r) s := by
  unfold spectralParameter
  fun_prop

theorem spectralParameter_real (r t : ℝ) :
    spectralParameter r (t : ℂ) = ((r * (1 - 4 * t ^ 2) : ℝ) : ℂ) := by
  simp only [spectralParameter, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow]

theorem spectralParameter_of_im_zero (r : ℝ) {s : ℂ} (hs : s.im = 0) :
    spectralParameter r s = ((r * (1 - 4 * s.re ^ 2) : ℝ) : ℂ) := by
  have he : s = (s.re : ℂ) := Complex.ext rfl hs
  exact (congrArg (spectralParameter r) he).trans (spectralParameter_real r s.re)

theorem spectralParameter_im (r : ℝ) (s : ℂ) :
    (spectralParameter r s).im = -8 * r * s.re * s.im := by
  simp [spectralParameter, pow_two, Complex.mul_im, Complex.sub_im]
  ring

theorem spectralParameter_im_ne_zero {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : 0 < s.re) (hi : s.im ≠ 0) : (spectralParameter r s).im ≠ 0 := by
  rw [spectralParameter_im]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hr.ne') hs.ne') hi

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralInverse (j : V →L[ℂ] H) (r : ℝ) (s : ℂ) : V →L[ℂ] V :=
  Ring.inverse (pencil (j.adjoint.comp j) (spectralParameter r s))

def spectralCorrection (j : V →L[ℂ] H) (r : ℝ) (D : ℂ → H) (s : ℂ) : H :=
  -j (spectralInverse j r s (j.adjoint (D s)))

theorem spectralCorrection_eq_j_forcedVector (j : V →L[ℂ] H) (r : ℝ) (D : ℂ → H) (s : ℂ) :
    spectralCorrection j r D s = j (forcedVector j (spectralParameter r s) (D s)) := by
  simp only [spectralCorrection, spectralInverse, forcedVector, map_neg]

theorem spectralPencil_isUnit_of_half_lt (j : V →L[ℂ] H) (hj : ‖j‖ ≤ 1)
    {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : 1 / 2 < s.re) :
    IsUnit (pencil (j.adjoint.comp j) (spectralParameter r s)) := by
  by_cases hi : s.im = 0
  · rw [spectralParameter_of_im_zero r hi]
    apply pencil_adjoint_comp_isUnit_of_neg j hj
    exact mul_neg_of_pos_of_neg hr (by nlinarith [sq_nonneg (s.re - 1 / 2)])
  · exact pencil_isUnit_nonreal _ (adjoint_comp_selfAdjoint j) _
      (spectralParameter_im_ne_zero hr (lt_trans (by norm_num) hs) hi)

theorem spectralInverse_analyticAt_of_unit (j : V →L[ℂ] H) (r : ℝ) (s : ℂ)
    (hs : IsUnit (pencil (j.adjoint.comp j) (spectralParameter r s))) :
    AnalyticAt ℂ (spectralInverse j r) s :=
  (pencil_inverse_analyticAt_of_isUnit _ _ hs).comp_of_eq (spectralParameter_analyticAt r s) rfl

theorem spectralInverse_meromorphicAt (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (hF : ∀ t : ℝ, t < r → (pencil (j.adjoint.comp j) (t : ℂ)).IsFredholm)
    {s : ℂ} (hs : 0 < s.re) : MeromorphicAt (spectralInverse j r) s := by
  have hm : MeromorphicAt (fun z => Ring.inverse (pencil (j.adjoint.comp j) z))
      (spectralParameter r s) := by
    by_cases hi : s.im = 0
    · let t := r * (1 - 4 * s.re ^ 2)
      have ht : t < r := by
        change r * (1 - 4 * s.re ^ 2) < r
        rw [mul_sub, mul_one]
        exact sub_lt_self _ (mul_pos hr (mul_pos (by norm_num) (pow_pos hs 2)))
      rw [spectralParameter_of_im_zero r hi]
      change MeromorphicAt (fun z => Ring.inverse (pencil (j.adjoint.comp j) z)) (t : ℂ)
      by_cases hz : t + 1 = 0
      · have hz' : (t : ℂ) + 1 = 0 := by exact_mod_cast hz
        have hu : IsUnit (pencil (j.adjoint.comp j) (t : ℂ)) := by simp [pencil, hz']
        exact (pencil_inverse_analyticAt_of_isUnit _ _ hu).meromorphicAt
      · exact inverse_meromorphicAt _ (adjoint_comp_selfAdjoint j) t hz (hF t ht)
    · have hu := pencil_isUnit_nonreal _ (adjoint_comp_selfAdjoint j) _
        (spectralParameter_im_ne_zero hr hs hi)
      exact (pencil_inverse_analyticAt_of_isUnit _ _ hu).meromorphicAt
  exact hm.comp_analyticAt (spectralParameter_analyticAt r s)

theorem adjoint_apply_analyticAt (j : V →L[ℂ] H) {D : ℂ → H} {s : ℂ}
    (hD : AnalyticAt ℂ D s) : AnalyticAt ℂ (fun z => j.adjoint (D z)) s :=
  (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := H) (F := V) j.adjoint (D s)).comp_of_eq hD rfl

theorem forcedCorrection_analyticAt (j : V →L[ℂ] H) {A : ℂ → V →L[ℂ] V}
    {D : ℂ → H} {s : ℂ} (hA : AnalyticAt ℂ A s) (hD : AnalyticAt ℂ D s) :
    AnalyticAt ℂ (fun z => -j (A z (j.adjoint (D z)))) s := by
  have h := ((ContinuousLinearMap.apply ℂ V).analyticAt_bilinear (j.adjoint (D s), A s)).comp₂
    (adjoint_apply_analyticAt j hD) hA
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := V) (F := H)
    (-j) (A s (j.adjoint (D s)))).comp_of_eq h rfl

theorem spectralCorrection_meromorphicOn (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (hF : ∀ t : ℝ, t < r → (pencil (j.adjoint.comp j) (t : ℂ)).IsFredholm)
    (D : ℂ → H) (hD : ∀ s, AnalyticAt ℂ D s) :
    MeromorphicOn (spectralCorrection j r D) {s | 0 < s.re} := by
  intro s hs
  exact OAI.CubicEisenstein.meromorphicAt_clm (-j)
    (OAI.CubicEisenstein.meromorphicAt_clm_apply (spectralInverse_meromorphicAt j hr hF hs)
      (adjoint_apply_analyticAt j (hD s)).meromorphicAt)

theorem spectralCorrection_analyticOnNhd (j : V →L[ℂ] H) (hj : ‖j‖ ≤ 1)
    {r : ℝ} (hr : 0 < r) (D : ℂ → H) (hD : ∀ s, AnalyticAt ℂ D s) :
    AnalyticOnNhd ℂ (spectralCorrection j r D) {s | 1 / 2 < s.re} := by
  intro s hs
  exact forcedCorrection_analyticAt j
    (spectralInverse_analyticAt_of_unit j r s (spectralPencil_isUnit_of_half_lt j hj hr hs)) (hD s)

end
end ArtinMatthews.HilbertResolvent
