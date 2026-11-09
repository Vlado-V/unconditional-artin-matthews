module

public import ArtinMatthews.SourceNarrowGammaRatio
public import ArtinMatthews.SourceNarrowStripConvexity
public import ArtinMatthews.SourceRayAbsoluteBounds
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCriticalBound


set_option backward.privateInPublic true
@[expose] public section

/-! Conductor-sensitive growth for the actual primitive continuation on
all the numerator lines of source06. The boundary choices retain the
one-half conductor power already at real part .003. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField Complex VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]

variable {M : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
variable (hprim : IsPrimitiveOnIdeals ψ.residue) (hnp : ψ.IsNonprincipal)

include hnp in
theorem sourcePrimitiveContinued_narrow_right {s : ℂ} (hs : (1001/1000 : ℝ) ≤ s.re) :
    ‖ψ.primitiveContinued hM hprim s‖ ≤ sourceRayAbsoluteEulerBound F (1001/1000) := by
  rw [ψ.primitiveContinued_eq_dirichlet hM hprim hnp (by linarith : 1 < s.re)]
  exact (sourceRayDirichlet_norm_bounds F ψ (by norm_num) hs).1

include hnp in
theorem sourcePrimitiveContinued_narrow_left_norm (t : ℝ) :
    ‖ψ.primitiveContinued hM hprim ((-1/1000 : ℂ)+(t : ℂ)*I)‖ =
      (mixedConductorScale F (integralIdealFractionalUnit M hM))^(501/500 : ℝ) *
        ‖sourceNarrowGammaRatio F t‖ *
        ‖ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)
          ((1001/1000 : ℂ)-(t : ℂ)*I)‖ := by
  obtain ⟨W, hW, hfe⟩ := ψ.primitiveContinued_left_functionalEquation hM hprim hnp
  have hA := mixedConductorScale_pos F (integralIdealFractionalUnit M hM)
  have ha : 1-((-1/1000 : ℂ)+(t : ℂ)*I) = (1001/1000 : ℂ)-(t : ℂ)*I := by ring
  have hr : (1-2*((-1/1000 : ℂ)+(t : ℂ)*I)).re = (501/500 : ℝ) := by norm_num
  rw [hfe _ (by norm_num), ha]
  simp only [norm_mul, hW, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hA, sourceNarrowGammaRatio, hr]
  ring

/-- Exact conductor scale on the narrower strip, before taking a uniform power. -/
theorem exists_sourcePrimitiveContinued_narrow_strip :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧
      ∀ {N : Ideal (𝓞 F)} (θ : EvenIdealRayCharacter F N) (hN : N ≠ ⊥)
        (hθ : IsPrimitiveOnIdeals θ.residue) (_hnθ : θ.IsNonprincipal) (s : ℂ),
        -(1/1000 : ℝ) ≤ s.re → s.re ≤ 1001/1000 →
        ‖θ.primitiveContinued hN hθ s‖ ≤ C*
          (mixedConductorScale F (integralIdealFractionalUnit N hN))^(1001/1000-s.re)*
          (|s.im|+2)^m := by
  obtain ⟨C, m, hC, hΓ⟩ := exists_sourceNarrowGammaRatio_polynomial_bound F
  let R := sourceRayAbsoluteEulerBound F (1001/1000)
  have hR : 0 < R := sourceRayAbsoluteEulerBound_pos F _
  let B := C*R+R
  have hB : 0 < B := add_pos (mul_pos hC hR) hR
  refine ⟨B*6^m*(250/167)^m, m, by positivity, ?_⟩
  intro N θ hN hθ hnθ s hs hs'
  let A := mixedConductorScale F (integralIdealFractionalUnit N hN)
  have hA : 0 < A := mixedConductorScale_pos F _
  apply sourceNarrowStripConvexity hA hB m (θ.primitiveContinued_entire hN hθ) _ _
    (θ.primitiveContinued_convexity_strip_growth hN hθ hnθ) hs hs'
  · intro t
    rw [sourcePrimitiveContinued_narrow_left_norm F θ hN hθ hnθ]
    have hright := sourcePrimitiveContinued_narrow_right F θ.inverse hN (θ.inverse_isPrimitive hN hθ)
      (θ.inverse_isNonprincipal hnθ) (s := (1001/1000 : ℂ)-(t : ℂ)*I) (by norm_num)
    have hP : 0 ≤ A^(501/500 : ℝ) := Real.rpow_nonneg hA.le _
    have hB₁ : C*R ≤ B := le_add_of_nonneg_right hR.le
    calc
      _ ≤ (A^(501/500 : ℝ)*(C*(|t|+2)^m))*R :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hΓ t) hP) hright (norm_nonneg _) (by positivity)
      _ = (C*R)*A^(501/500 : ℝ)*(|t|+2)^m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB₁ hP) (by positivity)
  · intro t
    have hright := sourcePrimitiveContinued_narrow_right F θ hN hθ hnθ
      (s := (1001/1000 : ℂ)+(t : ℂ)*I) (by norm_num)
    have hB₂ : R ≤ B := le_add_of_nonneg_left (mul_nonneg hC.le hR.le)
    exact hright.trans (hB₂.trans (le_mul_of_one_le_right hB.le
      (one_le_pow₀ (by linarith [abs_nonneg t]))))

theorem sourceMixedConductorScale_pow_le {N : Ideal (𝓞 F)} (hN : N ≠ ⊥)
    {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    (mixedConductorScale F (integralIdealFractionalUnit N hN))^x ≤
      max 1 (mixedDiscriminantScale F)*(N.absNorm : ℝ)^(1/2 : ℝ) := by
  have hD := mixedDiscriminantScale_pos F
  have hQ : 1 ≤ (N.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hN)
  have hD' : (mixedDiscriminantScale F)^x ≤ max 1 (mixedDiscriminantScale F) := by
    simpa only [Real.rpow_one] using positive_rpow_le_max hD hx hx'
  rw [mixedConductorScale, Real.mul_rpow hD.le (Real.sqrt_nonneg _)]
  simp only [integralIdealFractionalUnit, Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _)]
  exact mul_le_mul hD' (Real.rpow_le_rpow_of_exponent_le hQ (by linarith))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (zero_le_one.trans (le_max_left _ _))

/-- The height degree depends only on the field. The primitive norm enters with power one half. -/
theorem exists_sourcePrimitiveContinued_source06_bound :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧
      ∀ {N : Ideal (𝓞 F)} (θ : EvenIdealRayCharacter F N) (hN : N ≠ ⊥)
        (hθ : IsPrimitiveOnIdeals θ.residue) (_hnθ : θ.IsNonprincipal) (s : ℂ),
        (3/1000 : ℝ) ≤ s.re →
        ‖θ.primitiveContinued hN hθ s‖ ≤ C*(N.absNorm : ℝ)^(1/2 : ℝ)*(|s.im|+2)^m := by
  obtain ⟨C, m, hC, h⟩ := exists_sourcePrimitiveContinued_narrow_strip F
  let D := max 1 (mixedDiscriminantScale F)
  let R := sourceRayAbsoluteEulerBound F (1001/1000)
  have hD : 1 ≤ D := le_max_left _ _
  have hR : 0 < R := sourceRayAbsoluteEulerBound_pos F _
  have hB : 0 < C*D+R := add_pos (mul_pos hC (zero_lt_one.trans_le hD)) hR
  refine ⟨C*D+R, m, hB, ?_⟩
  intro N θ hN hθ hnθ s hs
  have hQ : 1 ≤ (N.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hN)
  have hQ' : 1 ≤ (N.absNorm : ℝ)^(1/2 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hh : 1 ≤ (|s.im|+2)^m := one_le_pow₀ (by linarith [abs_nonneg s.im])
  by_cases hr : (1001/1000 : ℝ) ≤ s.re
  · refine (sourcePrimitiveContinued_narrow_right F θ hN hθ hnθ hr).trans ?_
    exact (le_add_of_nonneg_left (mul_nonneg hC.le (zero_le_one.trans hD))).trans
      ((le_mul_of_one_le_right hB.le hQ').trans (le_mul_of_one_le_right (by positivity) hh))
  · have hr' : s.re ≤ (1001/1000 : ℝ) := le_of_lt (lt_of_not_ge hr)
    have hscale := sourceMixedConductorScale_pow_le F hN
      (x := 1001/1000-s.re) (by linarith) (by linarith)
    calc
      _ ≤ C*(mixedConductorScale F (integralIdealFractionalUnit N hN))^(1001/1000-s.re)*
          (|s.im|+2)^m := h θ hN hθ hnθ s (by linarith) hr'
      _ ≤ C*(D*(N.absNorm : ℝ)^(1/2 : ℝ))*(|s.im|+2)^m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hC.le) (by positivity)
      _ = (C*D)*(N.absNorm : ℝ)^(1/2 : ℝ)*(|s.im|+2)^m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hR.le) (by positivity)) (by positivity)

end
end ArtinMatthews.SourceEulerAssembly
