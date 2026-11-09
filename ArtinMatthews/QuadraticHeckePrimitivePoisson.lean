module

public import ArtinMatthews.QuadraticHeckePrimitiveContour
public import ArtinMatthews.QuadraticHeckeIdealSmoothing
public import ArtinMatthews.QuadraticHeckeRootNumber
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
local notation "r" => InfinitePlace.nrComplexPlaces K
local notation "A" => quadraticHeckeFieldScale K

private theorem quadratic_poisson_scale {X Q : ℝ} (hX : 0 < X) (hQ : 0 < Q) (s : ℂ) :
    (X : ℂ) ^ (1 - s) * (Q : ℂ) ^ (s - 1/2) =
      (X / Real.sqrt Q : ℝ) * ((Q / X : ℝ) : ℂ) ^ s := by
  rw [positiveReal_cpow_eq_exp hX, positiveReal_cpow_eq_exp hQ,
    positiveReal_cpow_eq_exp (div_pos hQ hX), ← Complex.exp_add]
  have hc : ((X / Real.sqrt Q : ℝ) : ℂ) =
      Complex.exp ((Real.log (X / Real.sqrt Q) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (div_pos hX (Real.sqrt_pos.mpr hQ))]
  rw [hc, ← Complex.exp_add, Real.log_div hX.ne' (Real.sqrt_pos.mpr hQ).ne',
    Real.log_div hQ.ne' hX.ne', Real.log_sqrt hQ.le]
  push_cast
  congr 1
  ring

omit [IsTotallyComplex K] in
/-- Exact primitive quadratic Hecke norm Poisson with the actual coefficient
and dual profile. The phase is the primitive functional equation phase. -/
theorem quadraticHeckePrimitiveNormPoisson_of_reflection {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    (hprim : IsPrimitiveOnIdeals ψ.residue) (hnp : ψ.IsNonprincipal) (W : ℂ)
    (hfe : ∀ s : ℂ, 0 < s.re →
      ψ.primitiveContinued hM hprim (1 - s) =
        W * (Ideal.absNorm M : ℂ) ^ (s - 1 / 2) * quadraticHeckeDualGamma A r s *
          ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) s) :
    ∀ (w : ℝ → ℂ) (_hc : HasCompactSupport w)
      (_hp : tsupport w ⊆ Ioi 0) (_hs : ContDiff ℝ ∞ w) {X : ℝ} (_hX : 0 < X),
      (∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, ψ.allCoefficient J.val *
        w ((Ideal.absNorm J.val : ℝ) / X)) =
        W * (X / Real.sqrt (Ideal.absNorm M : ℝ) : ℝ) *
          ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, ψ.inverse.allCoefficient J.val *
            quadraticHeckeDualProfile A r w ((Ideal.absNorm J.val : ℝ) * X / (Ideal.absNorm M : ℝ)) := by
  intro w hc hp hs X hX
  let Q : ℝ := Ideal.absNorm M
  have hQ : 0 < Q := by
    change 0 < (Ideal.absNorm M : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  let L := ψ.primitiveContinued hM hprim
  let Li := ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)
  let D := quadraticHeckeDualMellin A r w
  let v (t : ℝ) : ℂ := (5/4 : ℂ) + (t : ℂ) * I
  let u (t : ℝ) : ℂ := (-1/4 : ℂ) + (t : ℂ) * I
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let k : ℂ := W * (X / Real.sqrt Q : ℝ)
  have hq (J : {J : Ideal (𝓞 K) // J ≠ ⊥}) : 0 < (Ideal.absNorm J.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr J.property)
  have hsmooth_source := quadraticHeckeIdealSmoothing_contour K ψ hM hprim hnp
    (mellin w) (σ := 5 / 4) (by norm_num)
    ((smoothMellin_entire w hc hp hs.continuous).continuous.comp (by fun_prop))
    (smoothMellin_verticalIntegrable w hc hp hs _) hX
  have hsource : (∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, ψ.allCoefficient J.val *
        w ((Ideal.absNorm J.val : ℝ) / X)) =
      c * ∫ t : ℝ, (X : ℂ) ^ v t * mellin w (v t) * L (v t) := by
    simpa only [smoothMellin_inversion w hc hp hs (5/4) (div_pos (hq _) hX),
      c, v, L, Complex.ofReal_div, Complex.ofReal_ofNat] using hsmooth_source
  have hDc : Continuous (fun t : ℝ => D (v t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hv : ContinuousAt v t := by unfold v; fun_prop
    exact (quadraticHeckeDualMellin_differentiableAt A r w hc hp hs.continuous (v t)
      (by norm_num [v])).continuousAt.comp' (f := v) (x := t) hv
  have hDi : Integrable (fun t : ℝ => D (v t)) := by
    simpa only [D, v, Complex.ofReal_div, Complex.ofReal_ofNat] using
      quadraticHeckeDualMellin_verticalIntegrable A r w hc hp hs (σ := 5/4) (by norm_num)
  have hsmooth_dual := quadraticHeckeIdealSmoothing_contour K ψ.inverse hM
    (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) D (σ := 5/4) (by norm_num)
    (by simpa only [v, Complex.ofReal_div, Complex.ofReal_ofNat] using hDc)
    (by simpa only [v, Complex.ofReal_div, Complex.ofReal_ofNat] using hDi) (div_pos hQ hX)
  have hprofile (J : {J : Ideal (𝓞 K) // J ≠ ⊥}) :
      mellinInv (5/4) D ((Ideal.absNorm J.val : ℝ) / (Q / X)) =
        quadraticHeckeDualProfile A r w ((Ideal.absNorm J.val : ℝ) * X / Q) := by
    rw [div_div_eq_mul_div, ← quadraticHeckeDualProfileAt_eq_mellinInv]
    exact (quadraticHeckeDualProfileAt_eq A r w hc hp hs (σ := 1/2) (τ := 5/4)
      (by norm_num) (by norm_num) (div_pos (mul_pos (hq J) hX) hQ)).symm
  have hdual : (∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, ψ.inverse.allCoefficient J.val *
        quadraticHeckeDualProfile A r w ((Ideal.absNorm J.val : ℝ) * X / Q)) =
      c * ∫ t : ℝ, ((Q / X : ℝ) : ℂ) ^ v t * D (v t) * Li (v t) := by
    simpa only [hprofile, c, v, Li, Complex.ofReal_div, Complex.ofReal_ofNat] using hsmooth_dual
  have hline := quadraticHeckePrimitive_vertical_integral K ψ hM hprim hnp w hc hp hs hX
  change (∫ t : ℝ, (X : ℂ) ^ u t * mellin w (u t) * L (u t)) =
    ∫ t : ℝ, (X : ℂ) ^ v t * mellin w (v t) * L (v t) at hline
  have he (t : ℝ) : (X : ℂ) ^ u t * mellin w (u t) * L (u t) =
      k * (((Q / X : ℝ) : ℂ) ^ v (-t) * D (v (-t)) * Li (v (-t))) := by
    have huv : u t = 1 - v (-t) := by unfold u v; push_cast; ring
    have hreflection := hfe (v (-t)) (by norm_num [v])
    change L (1 - v (-t)) =
      W * (Q : ℂ) ^ (v (-t) - 1/2) * quadraticHeckeDualGamma A r (v (-t)) *
        Li (v (-t)) at hreflection
    rw [huv, hreflection]
    have hscale := quadratic_poisson_scale hX hQ (v (-t))
    change (X : ℂ) ^ (1 - v (-t)) * (Q : ℂ) ^ (v (-t) - 1/2) = _ at hscale
    unfold k D quadraticHeckeDualMellin
    calc
      _ = W * ((X : ℂ) ^ (1 - v (-t)) * (Q : ℂ) ^ (v (-t) - 1/2)) *
          (quadraticHeckeDualGamma A r (v (-t)) * mellin w (1 - v (-t))) * Li (v (-t)) := by
        ring
      _ = _ := by rw [hscale]; ring
  change _ = k * _
  rw [hsource, hdual, ← hline]
  simp_rw [he]
  rw [integral_const_mul, integral_neg_eq_self
    (f := fun t : ℝ => ((Q / X : ℝ) : ℂ) ^ v t * D (v t) * Li (v t))]
  ring

theorem quadraticHeckePrimitiveNormPoisson {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    (hprim : IsPrimitiveOnIdeals ψ.residue) (hnp : ψ.IsNonprincipal) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ (w : ℝ → ℂ) (_hc : HasCompactSupport w)
      (_hp : tsupport w ⊆ Ioi 0) (_hs : ContDiff ℝ ∞ w) {X : ℝ} (_hX : 0 < X),
      (∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, ψ.allCoefficient J.val *
        w ((Ideal.absNorm J.val : ℝ) / X)) =
        W * (X / Real.sqrt (Ideal.absNorm M : ℝ) : ℝ) *
          ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, ψ.inverse.allCoefficient J.val *
            quadraticHeckeDualProfile A r w ((Ideal.absNorm J.val : ℝ) * X / (Ideal.absNorm M : ℝ)) := by
  obtain ⟨W, hW, hfe⟩ := quadraticHeckePrimitiveReflection K ψ hM hprim hnp
  exact ⟨W, hW, quadraticHeckePrimitiveNormPoisson_of_reflection K ψ hM hprim hnp W hfe⟩

theorem quadraticHeckePrimitiveNormPoisson_of_zeta_quotient
    (E : Type) [Field E] [NumberField E] {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    (hprim : IsPrimitiveOnIdeals ψ.residue) (hnp : ψ.IsNonprincipal)
    (hself : ∀ s, ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) s =
      ψ.primitiveContinued hM hprim s)
    (hEuler : ∀ s : ℂ, 1 < s.re → dedekindZeta E s = dedekindZeta K s * ψ.dirichlet s)
    (w : ℝ → ℂ) (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0)
    (hs : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, ψ.allCoefficient J.val *
      w ((Ideal.absNorm J.val : ℝ) / X)) =
      (X / Real.sqrt (Ideal.absNorm M : ℝ) : ℝ) *
        ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, ψ.inverse.allCoefficient J.val *
          quadraticHeckeDualProfile A r w ((Ideal.absNorm J.val : ℝ) * X / (Ideal.absNorm M : ℝ)) := by
  have hfe := quadraticHeckePrimitiveReflection_one_of_zeta_quotient K E ψ hM hprim hnp hself hEuler
  have hfe' (s : ℂ) (hs : 0 < s.re) :
      ψ.primitiveContinued hM hprim (1 - s) =
        1 * (Ideal.absNorm M : ℂ) ^ (s - 1 / 2) * quadraticHeckeDualGamma A r s *
          ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) s := by
    rw [one_mul, hself]
    exact hfe s hs
  simpa only [one_mul] using
    quadraticHeckePrimitiveNormPoisson_of_reflection K ψ hM hprim hnp 1 hfe' w hc hp hs hX

end
end ArtinMatthews
