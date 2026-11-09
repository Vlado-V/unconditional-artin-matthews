module

public import ArtinMatthews.PrincipalDedekindSourceReciprocal
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaRatioGlobal
public import ArtinMatthews.VaryingKummerAnalyticMixedInverseGammaStripGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Actual principal numerator boundary bounds for the Gaussian probe.
The filled zeta function is used throughout; no nonprincipal or zero-free
input is used in the functional equation or the growth estimates. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set Filter
open scoped NumberField Classical Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem principalDedekindRegularized_eq_inverseGamma {s : ℂ} (hs : s ≠ 0) :
    principalDedekindRegularized K s =
      (mixedDiscriminantScale K : ℂ)^(-s) * mixedInverseGammaFactor K s *
        mixedCompletedDedekindXi K s / s := by
  rw [principalDedekindRegularized, mixedDedekindEntireNumerator_eq_regularized K hs,
    mixedRegularizedDedekindZeta, Complex.cpow_neg]
  ring

theorem principalDedekindRegularized_left_reflection {s : ℂ} (hs : s.re < 0) :
    principalDedekindRegularized K s =
      (s-1) * (mixedDiscriminantScale K : ℂ)^(1-2*s) *
        mixedGammaFactor K (1-s) * mixedInverseGammaFactor K s *
          dedekindZeta K (1-s) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have ht : 1 < (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hD : (mixedDiscriminantScale K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'
  have hp : (mixedDiscriminantScale K : ℂ)^(-s) *
      (mixedDiscriminantScale K : ℂ)^(1-s) =
        (mixedDiscriminantScale K : ℂ)^(1-2*s) := by
    rw [← Complex.cpow_add _ _ hD]
    congr 1
    ring
  rw [principalDedekindRegularized_eq_inverseGamma K hs0,
    mixedCompletedDedekindXi_functional_equation,
    mixedCompletedDedekindXi_eq K ht]
  calc
    _ = ((mixedDiscriminantScale K : ℂ)^(-s) *
        (mixedDiscriminantScale K : ℂ)^(1-s)) *
        ((s-1) * mixedGammaFactor K (1-s) * mixedInverseGammaFactor K s *
          dedekindZeta K (1-s)) := by field_simp; ring
    _ = _ := by rw [hp]; ring

theorem dedekindZeta_norm_le_principalSourceBound {s : ℂ} (hs : 5/4 ≤ s.re) :
    ‖dedekindZeta K s‖ ≤ principalSourceReciprocalBound K := by
  rw [← exp_dedekindEulerLog_eq_dedekindZeta K (by linarith), Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (dedekindEulerLog_norm_le K hs))

theorem principalDedekindRegularized_left_line_norm (t : ℝ) :
    ‖principalDedekindRegularized K ((-1/4 : ℂ)+(t : ℂ)*I)‖ =
      ‖((-1/4 : ℂ)+(t : ℂ)*I)-1‖ * (mixedDiscriminantScale K)^(3/2 : ℝ) *
        ‖mixedGammaLeftRatio K t‖ * ‖dedekindZeta K ((5/4 : ℂ)-(t : ℂ)*I)‖ := by
  have h := principalDedekindRegularized_left_reflection K
    (s := (-1/4 : ℂ)+(t : ℂ)*I) (by norm_num)
  have ht : 1-((-1/4 : ℂ)+(t : ℂ)*I) = (5/4 : ℂ)-(t : ℂ)*I := by ring
  rw [ht] at h
  have he : principalDedekindRegularized K ((-1/4 : ℂ)+(t : ℂ)*I) =
      (((-1/4 : ℂ)+(t : ℂ)*I)-1) *
        (mixedDiscriminantScale K : ℂ)^(1-2*((-1/4 : ℂ)+(t : ℂ)*I)) *
          mixedGammaLeftRatio K t * dedekindZeta K ((5/4 : ℂ)-(t : ℂ)*I) := by
    rw [h, mixedGammaLeftRatio]
    ring
  rw [he, norm_mul, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (mixedDiscriminantScale_pos K)]
  congr 3
  norm_num

theorem exists_principalDedekindRegularized_boundary_bounds :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧ 1 ≤ m ∧
      (∀ t : ℝ, ‖principalDedekindRegularized K ((-1/4 : ℂ)+(t : ℂ)*I)‖ ≤
        C*(mixedDiscriminantScale K)^(3/2 : ℝ)*(|t|+2)^m) ∧
      ∀ t : ℝ, ‖principalDedekindRegularized K ((5/4 : ℂ)+(t : ℂ)*I)‖ ≤
        C*(|t|+2)^m := by
  obtain ⟨C,m,hC,hGamma⟩ := exists_mixedGammaLeftRatio_polynomial_bound K
  let B := (C+1)*principalSourceReciprocalBound K
  have hB : 0 < B := mul_pos (by linarith) (principalSourceReciprocalBound_pos K)
  refine ⟨B,m+1,hB,by omega,?_,?_⟩
  · intro t
    have hs : ‖((-1/4 : ℂ)+(t : ℂ)*I)-1‖ ≤ |t|+2 := by
      have h := Complex.norm_le_abs_re_add_abs_im (((-1/4 : ℂ)+(t : ℂ)*I)-1)
      norm_num at h
      linarith
    rw [principalDedekindRegularized_left_line_norm]
    have hz := dedekindZeta_norm_le_principalSourceBound K
      (s := (5/4 : ℂ)-(t : ℂ)*I) (by norm_num)
    have hbase : 0 ≤ |t|+2 := by positivity
    have hscale := Real.rpow_nonneg (mixedDiscriminantScale_pos K).le (3/2 : ℝ)
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hs hscale)
      (mul_le_mul (hGamma t) hz (norm_nonneg _) (mul_nonneg hC.le (pow_nonneg hbase m)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hbase hscale)
    have hCB : C*principalSourceReciprocalBound K ≤ B := by
      dsimp [B]
      nlinarith [principalSourceReciprocalBound_pos K]
    calc
      _ ≤ ((|t|+2)*(mixedDiscriminantScale K)^(3/2 : ℝ)) *
          ((C*(|t|+2)^m)*principalSourceReciprocalBound K) := by
        convert h using 1; ring
      _ = (C*principalSourceReciprocalBound K) *
          ((mixedDiscriminantScale K)^(3/2 : ℝ)*(|t|+2)^(m+1)) := by rw [pow_succ]; ring
      _ ≤ B*((mixedDiscriminantScale K)^(3/2 : ℝ)*(|t|+2)^(m+1)) :=
        mul_le_mul_of_nonneg_right hCB (mul_nonneg hscale (pow_nonneg hbase _))
      _ = _ := by ring
  · intro t
    rw [principalDedekindRegularized_eq_series K (by norm_num), norm_mul]
    have hs : ‖((5/4 : ℂ)+(t : ℂ)*I)-1‖ ≤ |t|+2 := by
      have h := Complex.norm_le_abs_re_add_abs_im (((5/4 : ℂ)+(t : ℂ)*I)-1)
      norm_num at h
      linarith
    have hz := dedekindZeta_norm_le_principalSourceBound K
      (s := (5/4 : ℂ)+(t : ℂ)*I) (by norm_num)
    have hCB : principalSourceReciprocalBound K ≤ B := by
      dsimp [B]
      nlinarith [principalSourceReciprocalBound_pos K]
    have hp : 1 ≤ (|t|+2)^m := one_le_pow₀ (by linarith [abs_nonneg t])
    have hbase : 0 ≤ |t|+2 := by positivity
    have hRB : principalSourceReciprocalBound K ≤ B*(|t|+2)^m :=
      hCB.trans (le_mul_of_one_le_right hB.le hp)
    calc
      _ ≤ (|t|+2)*principalSourceReciprocalBound K := mul_le_mul hs hz (norm_nonneg _) hbase
      _ ≤ (|t|+2)*(B*(|t|+2)^m) := mul_le_mul_of_nonneg_left hRB hbase
      _ = _ := by rw [pow_succ]; ring

end
end ArtinMatthews.VaryingKummerAnalytic
