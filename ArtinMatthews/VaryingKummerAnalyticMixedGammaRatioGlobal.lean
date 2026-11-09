module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaRatio
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaConjugation


set_option backward.privateInPublic true
@[expose] public section

/-! All-height polynomial control of the actual Gamma ratio on the left
boundary Re(s)=-1/4. The bounded-height part comes from a concrete continuous
Gamma/inverse-Gamma product; the unbounded-height part uses the proved
logarithmic derivative estimate. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
open scoped NumberField nonZeroDivisors Classical ComplexConjugate
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedGammaLeftRatio (t : ℝ) : ℂ :=
  mixedGammaFactor K ((5/4 : ℂ)-(t : ℂ)*I) *
    mixedInverseGammaFactor K ((-1/4 : ℂ)+(t : ℂ)*I)

theorem mixedGammaLeftRatio_norm (t : ℝ) :
    ‖mixedGammaLeftRatio K t‖ =
      ‖mixedGammaFactor K ((5/4 : ℂ)+(t : ℂ)*I) *
        mixedInverseGammaFactor K ((-1/4 : ℂ)+(t : ℂ)*I)‖ := by
  have he : ((5/4 : ℂ)-(t : ℂ)*I) = conj ((5/4 : ℂ)+(t : ℂ)*I) := by
    simp only [map_add,map_div₀,map_ofNat,map_mul,Complex.conj_ofReal,Complex.conj_I]
    ring
  rw [mixedGammaLeftRatio,he,mixedGammaFactor_conj,norm_mul,norm_mul,norm_conj]

theorem mixedGammaLeftRatio_continuous : Continuous (mixedGammaLeftRatio K) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hG := (mixedGammaFactor_differentiableAt K
    (s := (5/4 : ℂ)-(t : ℂ)*I) (by norm_num)).continuousAt
  have hi := (mixedInverseGammaFactor_entire K ((-1/4 : ℂ)+(t : ℂ)*I)).continuousAt
  exact (hG.comp (f := fun u : ℝ => (5/4 : ℂ)-(u : ℂ)*I) (by fun_prop)).mul
    (hi.comp (f := fun u : ℝ => (-1/4 : ℂ)+(u : ℂ)*I) (by fun_prop))

theorem exists_mixedGammaLeftRatio_polynomial_bound :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧ ∀ t : ℝ,
      ‖mixedGammaLeftRatio K t‖ ≤ C*(|t|+2)^m := by
  obtain ⟨B,hB,hbound⟩ := exists_mixedGammaFactor_horizontal_ratio_bound
  obtain ⟨t₀,_ht₀,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
    (mixedGammaLeftRatio_continuous K).norm.continuousOn
  let C := ‖mixedGammaLeftRatio K t₀‖+1
  let m := Nat.ceil (B*(Module.finrank ℚ K : ℝ))
  refine ⟨C,m,by dsimp [C]; positivity,?_⟩
  intro t
  have hC : 1 ≤ C := by dsimp [C]; linarith [norm_nonneg (mixedGammaLeftRatio K t₀)]
  have hp : 1 ≤ (|t|+2)^m := one_le_pow₀ (by linarith [abs_nonneg t])
  by_cases ht : 1 ≤ |t|
  · calc
      ‖mixedGammaLeftRatio K t‖ ≤ (|t|+2)^(B*(Module.finrank ℚ K : ℝ)) := by
        rw [mixedGammaLeftRatio_norm]
        exact hbound K t ht
      _ ≤ (|t|+2)^m := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (Nat.le_ceil _)
      _ ≤ C*(|t|+2)^m := le_mul_of_one_le_left (by positivity) hC
  · have hm : t ∈ Icc (-1 : ℝ) 1 := by
      have H := abs_le.mp (le_of_lt (lt_of_not_ge ht))
      exact H
    have hsmall : ‖mixedGammaLeftRatio K t‖ ≤ ‖mixedGammaLeftRatio K t₀‖ := hmax hm
    have hc0 : 0 ≤ C := zero_le_one.trans hC
    exact hsmall.trans ((show ‖mixedGammaLeftRatio K t₀‖ ≤ C by dsimp [C]; linarith).trans
      (le_mul_of_one_le_right hc0 hp))

end
end ArtinMatthews.VaryingKummerAnalytic
