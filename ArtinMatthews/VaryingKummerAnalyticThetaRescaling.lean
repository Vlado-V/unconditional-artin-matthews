module

public import ArtinMatthews.VaryingKummerAnalyticMixedThetaPeriodicity


set_option backward.privateInPublic true
@[expose] public section

/-! Scaling of actual Gaussian theta continuations, including different lattice
coordinate types of the same real dimension. -/
namespace ArtinMatthews.ReusedTheta
open MeasureTheory Set
open scoped Classical BigOperators
noncomputable section

/-- The theta identity at positive Gaussian scale determines the exact entire
Mellin continuation, including its spectral power of the scale. -/
theorem thetaMellinXi_eq_of_normalizedTheta_rescale
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (C : EuclideanSpace ℝ κ ≃L[ℝ] EuclideanSpace ℝ κ)
    (hcard : Fintype.card ι = Fintype.card κ)
    {a : ℝ} (ha : 0 < a)
    (htheta : ∀ t : ℝ, normalizedTheta B t = normalizedTheta C (a*t)) (s : ℂ) :
    thetaMellinXi B s = (a : ℂ)^(-s) * thetaMellinXi C s := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hp : Differentiable ℂ (fun s : ℂ => (a : ℂ)^(-s) * thetaMellinXi C s) :=
    (Differentiable.const_cpow differentiable_id.neg (Or.inl ha0)).mul
      (thetaMellinXi_differentiable C)
  have H (z : ℂ) (hz : (Fintype.card ι : ℝ)/2 < z.re) :
      thetaMellinXi B z = (a : ℂ)^(-z) * thetaMellinXi C z := by
    have hz0 : z ≠ 0 := by
      intro he
      simp only [he, Complex.zero_re] at hz
      have : (0 : ℝ) ≤ (Fintype.card ι : ℝ)/2 := by positivity
      linarith
    have hzn : z ≠ (Fintype.card ι : ℂ)/2 := by
      intro he
      simp [he] at hz
    rw [thetaMellinXi_eq B hz0 hzn,
      thetaMellinXi_eq C hz0 (by simpa only [← hcard] using hzn),
      ← (normalizedTheta_hasMellin B hz).2,
      ← (normalizedTheta_hasMellin C (by simpa only [← hcard] using hz)).2]
    have hf : (fun t => normalizedTheta B t-1) =
        fun t => (fun v => normalizedTheta C v-1) (a*t) := by
      funext t
      rw [htheta]
    rw [hf, mellin_comp_mul_left (fun t : ℝ => normalizedTheta C t-1) z ha]
    simp only [hcard, smul_eq_mul]
    ring
  have he := ((thetaMellinXi_differentiable B).differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hp.differentiableOn.analyticOnNhd isOpen_univ)
    (z₀ := (Fintype.card ι : ℂ)/2+1) (by
      have hx : (Fintype.card ι : ℝ)/2 < ((Fintype.card ι : ℂ)/2+1).re := by simp
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx] with z hz
      exact H z hz)
  exact congrFun he s

end
end ArtinMatthews.ReusedTheta
