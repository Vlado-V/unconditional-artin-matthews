module

public import ArtinMatthews.QuadraticHeckeDualProfile
public import ArtinMatthews.VaryingKummerAnalyticConductorConvexity


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory SourcePhysical VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField ContDiff Classical
noncomputable section

private theorem rpow_le_endpoints {x a b v : ℝ} (hx : 0 < x) (hav : a ≤ v) (hvb : v ≤ b) :
    x ^ v ≤ max (x ^ a) (x ^ b) := by
  rcases le_total x 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge hx h hav).trans (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le h hvb).trans (le_max_right _ _)

variable (K : Type) [Field K] [NumberField K]

/-- The contour of the smoothed entire primitive Hecke function moves
from the absolutely convergent line to the dual line. -/
theorem quadraticHeckePrimitive_vertical_integral {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    (hprim : IsPrimitiveOnIdeals ψ.residue) (hnp : ψ.IsNonprincipal)
    (w : ℝ → ℂ) (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0)
    (hs : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    let f := fun z : ℂ => (X : ℂ) ^ z * mellin w z * ψ.primitiveContinued hM hprim z
    (∫ t : ℝ, f ((-1/4 : ℂ) + t * I)) = ∫ t : ℝ, f ((5/4 : ℂ) + t * I) := by
  dsimp only
  let a : ℝ := -1 / 4
  let b : ℝ := 5 / 4
  let A := mixedConductorScale K (integralIdealFractionalUnit M hM)
  let f := fun z : ℂ => (X : ℂ) ^ z * mellin w z * ψ.primitiveContinued hM hprim z
  obtain ⟨C,m,hC,hL⟩ := exists_primitiveContinued_conductor_convexity K
  obtain ⟨B,hB,hW⟩ := smoothMellin_strip_decay w hc hp hs a b (m+2)
  have hA : 0 < A := mixedConductorScale_pos K _
  let E := max (X ^ a) (X ^ b)
  let D := C * max 1 (A ^ (3 / 2 : ℝ))
  have hD : 0 < D := mul_pos hC (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hE : 0 ≤ E := (Real.rpow_nonneg hX.le _).trans (le_max_left _ _)
  have hhol : Differentiable ℂ f := by
    exact ((differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      (smoothMellin_entire w hc hp hs.continuous)).mul (ψ.primitiveContinued_entire hM hprim)
  have H := source_vertical_integral_eq_of_heightWeight f
    (a := a) (b := b) (C := E * D * (2 ^ m * B)) (by norm_num [a,b]) hhol.differentiableOn
    (fun x hx t => by
      let z : ℂ := (x : ℂ) + (t : ℂ) * I
      have hzRe : z.re = x := by simp [z]
      have hzIm : z.im = t := by simp [z]
      have hXz : ‖(X : ℂ) ^ z‖ ≤ E := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hzRe]
        exact rpow_le_endpoints hX hx.1 hx.2
      have hAz : A ^ (5/4-z.re) ≤ max 1 (A ^ (3/2 : ℝ)) := by
        have h₁ : 0 ≤ 5/4-z.re := by
          rw [hzRe]
          exact sub_nonneg.mpr hx.2
        have h₂ : 5/4-z.re ≤ 3/2 := by
          rw [hzRe]
          have hl : (-1 / 4 : ℝ) ≤ x := hx.1
          linarith
        simpa only [Real.rpow_zero] using rpow_le_endpoints hA h₁ h₂
      have hleft : -(1/4 : ℝ) ≤ z.re := by simpa [hzRe, a, neg_div] using hx.1
      have hright : z.re ≤ 5/4 := hzRe ▸ hx.2
      have hLz := hL ψ hM hprim hnp z hleft hright
      rw [hzIm] at hLz
      have hLz' : ‖ψ.primitiveContinued hM hprim z‖ ≤ D*(|t|+2)^m :=
        hLz.trans (by unfold D; gcongr)
      have hWz := hW z (hzRe ▸ hx.1) (hzRe ▸ hx.2)
      rw [hzIm] at hWz
      have hrapid := sourceContourHeightWeight_of_rapid m t B _ (norm_nonneg _) hWz
      change ‖f z‖ ≤ _
      unfold f
      rw [norm_mul, norm_mul]
      calc
        _ ≤ E * ‖mellin w z‖ * (D*(|t|+2)^m) := by gcongr
        _ = (E*D)*((|t|+2)^m*‖mellin w z‖) := by ring
        _ ≤ _ := by rw [mul_assoc (E*D)]; exact mul_le_mul_of_nonneg_left hrapid (by positivity))
  simpa only [a, b, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_ofNat] using H

end
end ArtinMatthews
