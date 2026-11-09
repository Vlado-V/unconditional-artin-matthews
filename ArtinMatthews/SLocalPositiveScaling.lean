module

public import ArtinMatthews.SLocalLogarithm


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source scaling ell_T has finite components one and
the same positive real component T^(1/[K:Q]) at every complex place.
Its genuine product-formula norm is T. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SUnitGroup
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]

private def positiveComplexLocal (w : InfinitePlace K) (hw : w.IsComplex) (t : ℝ) : w.Completionˣ :=
  Units.mapEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMulEquiv
    (Units.mk0 ((Real.exp t : ℝ) : ℂ) (by exact_mod_cast (Real.exp_ne_zero t)))

omit [NumberField K] in
private theorem positiveComplexLocal_norm (w : InfinitePlace K) (hw : w.IsComplex) (t : ℝ) :
    ‖(positiveComplexLocal K w hw t : w.Completion)‖ = Real.exp t := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  change ‖e.symm ((Real.exp t : ℝ) : ℂ)‖ = Real.exp t
  calc
    _ = ‖e (e.symm ((Real.exp t : ℝ) : ℂ))‖ :=
      ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry.norm_map_of_map_zero
        (map_zero e) _).symm
    _ = Real.exp t := by
      rw [e.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos t).le]

def sLocalPositiveScaling {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : ℝ) : SWholeUnits K S :=
  (fun w => positiveComplexLocal K w
    ((source_isTotallyComplex K hζ).isComplex w)
    (Real.log T / (Module.finrank ℚ K : ℝ)), fun _ => 1)

theorem sLocalPositiveScaling_finite {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : ℝ) (v : S) :
    (sLocalPositiveScaling K hζ S T).2 v = 1 := rfl

theorem sLocalPositiveScaling_infinite_norm {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : ℝ) (w : InfinitePlace K) :
    ‖((sLocalPositiveScaling K hζ S T).1 w : w.Completion)‖ =
      Real.exp (Real.log T / (Module.finrank ℚ K : ℝ)) :=
  positiveComplexLocal_norm K w _ _

theorem sLocalPositiveScaling_norm {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {T : ℝ} (hT : 0 < T) :
    sLocalNorm K S (sLocalPositiveScaling K hζ S T) = T := by
  have hdeg : (∑ w : InfinitePlace K, (w.mult : ℝ)) = (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (InfinitePlace.sum_mult_eq (K := K))
  have hdeg0 : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  unfold sLocalNorm sLocalLogSum
  change Real.exp (∑ p : LogPlace (K := K) S,
    sLocalLog K S (Additive.ofMul (sLocalPositiveScaling K hζ S T)) p) = T
  rw [Fintype.sum_sum_type]
  have hsum : (∑ w : InfinitePlace K,
      sLocalLog K S (Additive.ofMul (sLocalPositiveScaling K hζ S T)) (Sum.inl w)) = Real.log T := by
    change (∑ w : InfinitePlace K, (w.mult : ℝ) *
      Real.log ‖((sLocalPositiveScaling K hζ S T).1 w : w.Completion)‖) = _
    simp only [sLocalPositiveScaling_infinite_norm, Real.log_exp]
    rw [← Finset.sum_mul, hdeg, mul_div_cancel₀ (Real.log T) hdeg0]
  have hfinite : (∑ v : S,
      sLocalLog K S (Additive.ofMul (sLocalPositiveScaling K hζ S T)) (Sum.inr v)) = 0 := by
    change (∑ v : S, Real.log ‖((sLocalPositiveScaling K hζ S T).2 v : v.1.adicCompletion K)‖) = 0
    simp only [sLocalPositiveScaling_finite, Units.val_one, norm_one, Real.log_one, Finset.sum_const_zero]
  rw [hsum, hfinite, add_zero, Real.exp_log hT]

end
end ArtinMatthews
