module

public import ArtinMatthews.QuadraticHeckeDualMellin
public import ArtinMatthews.SourceContourHeightWeight
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Complex Set SourcePhysical
open scoped ContDiff Topology
noncomputable section

def quadraticHeckeDualIntegrand (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (-s) * quadraticHeckeDualMellin A r w s

def quadraticHeckeDualProfileAt (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (σ x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t : ℝ, quadraticHeckeDualIntegrand A r w x ((σ : ℂ) + (t : ℂ) * I)

def quadraticHeckeDualProfile (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (x : ℝ) : ℂ :=
  quadraticHeckeDualProfileAt A r w (1 / 2) x

theorem quadraticHeckeDualIntegrand_differentiableAt (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hcontinuous : Continuous w) {x : ℝ} (hx : 0 < x) (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (quadraticHeckeDualIntegrand A r w x) s := by
  let : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := by fun_prop
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) s :=
    (differentiableAt_const_cpow_of_neZero x (-s)).comp s hneg
  exact hpow.mul (quadraticHeckeDualMellin_differentiableAt A r w hcompact hpositive hcontinuous s hs)

private theorem quadraticHeckeDualIntegrand_height_bound (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ τ : ℝ} (hσ : 1 / 4 ≤ σ) (_hστ : σ ≤ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → ∀ v ∈ Icc σ τ, ∀ t : ℝ,
      ‖quadraticHeckeDualIntegrand A r w x ((v : ℂ) + (t : ℂ) * I)‖ ≤
        (C * max (x ^ (-σ)) (x ^ (-τ))) * sourceContourHeightWeight t := by
  obtain ⟨B, hB⟩ := exists_nat_gt τ
  obtain ⟨C, hC, hdecay⟩ := quadraticHeckeDualMellin_strip_decay A r B w hcompact hpositive hsmooth 2
  refine ⟨C, hC, ?_⟩
  intro x hx v hv t
  let s := (v : ℂ) + (t : ℂ) * I
  have hsRe : s.re = v := by simp [s]
  have hsIm : s.im = t := by simp [s]
  have h := hdecay s (by rw [hsRe]; exact hσ.trans hv.1)
    (by rw [hsRe]; linarith [hv.2])
  rw [hsIm] at h
  have hc := sourceContourHeightWeight_of_rapid 0 t C ‖quadraticHeckeDualMellin A r w s‖
    (norm_nonneg _) h
  simp only [pow_zero, one_mul] at hc
  have hp : x ^ (-v) ≤ max (x ^ (-σ)) (x ^ (-τ)) := by
    rcases le_total x 1 with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (neg_le_neg hv.2)).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg hv.1)).trans (le_max_left _ _)
  change ‖quadraticHeckeDualIntegrand A r w x s‖ ≤ _
  rw [quadraticHeckeDualIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.neg_re, hsRe]
  exact (mul_le_mul hp hc (norm_nonneg _) ((Real.rpow_nonneg hx.le _).trans (le_max_left _ _))).trans_eq
    (by ring)

theorem quadraticHeckeDualProfileAt_eq (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ τ x : ℝ} (hσ : 1 / 4 ≤ σ) (hστ : σ ≤ τ) (hx : 0 < x) :
    quadraticHeckeDualProfileAt A r w σ x = quadraticHeckeDualProfileAt A r w τ x := by
  obtain ⟨C, _, hC⟩ := quadraticHeckeDualIntegrand_height_bound A r w
    hcompact hpositive hsmooth hσ hστ
  unfold quadraticHeckeDualProfileAt
  congr 1
  apply source_vertical_integral_eq_of_heightWeight (C := C * max (x ^ (-σ)) (x ^ (-τ))) _ hστ
  · intro s hs
    exact (quadraticHeckeDualIntegrand_differentiableAt A r w hcompact hpositive hsmooth.continuous
      hx s (by linarith [hs.1])).differentiableWithinAt
  · exact hC x hx

theorem quadraticHeckeDualProfile_power_bound (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ : ℝ} (hσ : 1 / 4 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖quadraticHeckeDualProfile A r w x‖ ≤ C * x ^ (-σ) := by
  obtain ⟨C, hC, hbound⟩ := quadraticHeckeDualIntegrand_height_bound A r w
    hcompact hpositive hsmooth hσ (le_refl σ)
  let c : ℂ := 1 / (2 * Real.pi)
  refine ⟨‖c‖ * C * ∫ t : ℝ, sourceContourHeightWeight t,
    mul_nonneg (mul_nonneg (norm_nonneg _) hC.le)
      (integral_nonneg sourceContourHeightWeight_nonneg), ?_⟩
  intro x hx
  have he : quadraticHeckeDualProfile A r w x = quadraticHeckeDualProfileAt A r w σ x := by
    unfold quadraticHeckeDualProfile
    rcases le_total (1 / 2 : ℝ) σ with h | h
    · exact quadraticHeckeDualProfileAt_eq A r w hcompact hpositive hsmooth (by norm_num) h hx
    · exact (quadraticHeckeDualProfileAt_eq A r w hcompact hpositive hsmooth hσ h hx).symm
  rw [he, quadraticHeckeDualProfileAt, norm_mul]
  have hb := norm_integral_le_of_norm_le (sourceContourHeightWeight_integrable.const_mul (C * x ^ (-σ)))
    (ae_of_all _ (fun t => by simpa only [max_self] using hbound x hx σ ⟨le_rfl, le_rfl⟩ t))
  rw [integral_const_mul] at hb
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg c)).trans_eq (by ring)

end
end ArtinMatthews
