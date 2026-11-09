module

public import ArtinMatthews.VaryingKummerAnalyticMixedExplicitFormula
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinZeroRegion


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform error terms in the actual smoothed Dedekind explicit formula.
The zero-free region remains an explicit separate input to the final estimate;
this file does not assert it for the varying Kummer family. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped ContDiff BigOperators
noncomputable section
universe u

theorem mixedDedekindZeroOrder_norm_le_degree
    (K : Type*) [Field K] [NumberField K] :
    ‖(((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)‖ ≤
      (Module.finrank ℚ K : ℝ) := by
  have hc : 1 ≤ InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos)
  have hn := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  have hz : (0 : ℤ) ≤ (InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 := by omega
  rw [Complex.norm_intCast,abs_of_nonneg (Int.cast_nonneg hz)]
  exact_mod_cast (show (InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 ≤
    (Module.finrank ℚ K : ℤ) by omega)

/-- The actual explicit-formula remainder after retaining its true zero sum.
No zero-free hypothesis is required for this error bound. -/
theorem dedekindPrimePower_explicitFormula_uniform_error
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ A : ℝ,0 < A ∧ ∀ (K : Type u) [Field K] [NumberField K],∀ x : ℝ,0 < x →
      ‖(∑' i : DedekindPrimePowerIndex K,
        (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x)) -
        (x : ℂ)*mellin f 1 +
        (∑' ρ,(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ) +
        (((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0‖ ≤
        A*x^(-(1/2 : ℝ))*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)) := by
  obtain ⟨A,hA,hleft⟩ := exists_mixedMellin_left_integral_bound f hcompact hpositive hsmooth
  refine ⟨A,hA,?_⟩
  intro K _ _ x hx
  rw [dedekindPrimePower_explicitFormula K f hcompact hpositive hsmooth hx]
  convert (hleft K x hx).2 using 1
  congr 1
  ring

/-- The paper's smooth prime-ideal estimate, with its exact zero-location
input and a constant depending only on the smooth weight. -/
theorem dedekindPrimePower_smoothed_bound_of_zero_region
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ C : ℝ,0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      ∀ (x β : ℝ),1 ≤ x → 0 ≤ β →
      (∀ ρ : ℂ,mixedCompletedDedekindXi K ρ = 0 → ρ.re ≤ β) →
      ‖∑' i : DedekindPrimePowerIndex K,
        (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x)‖ ≤
        C*(x+x^β*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ))) := by
  obtain ⟨A,hA,hleft⟩ := exists_mixedMellin_left_integral_bound f hcompact hpositive hsmooth
  obtain ⟨B,hB,hzero⟩ := mixedCompletedDedekindXi_mellin_power_zero_region f hcompact hpositive hsmooth
  refine ⟨‖mellin f 1‖+B+‖mellin f 0‖+A+1,by positivity,?_⟩
  intro K _ _ x β hx hβ hregion
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let d : ℝ := Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)
  have hd : 0 ≤ d := add_nonneg (discr_log_nonneg K) (Nat.cast_nonneg _)
  have hn : (Module.finrank ℚ K : ℝ) ≤ d := le_add_of_nonneg_left (discr_log_nonneg K)
  have hpow : 1 ≤ x^β := Real.one_le_rpow hx hβ
  have hleftbound := (hleft K x hxpos).2
  have hsmall : x^(-(1/2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hL : ‖((1/(2*Real.pi) : ℝ) : ℂ)*
      ∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)‖ ≤ A*x^β*d := by
    apply hleftbound.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsmall.trans hpow) hA.le) hd
  obtain ⟨C0,hC0,hconv⟩ := mixedCompletedDedekindXi_mellin_power_zero_uniform f hcompact hpositive hsmooth
  have hZ : ‖∑' ρ,(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ‖ ≤ B*x^β*d :=
    (norm_tsum_le_tsum_norm (hconv K x hxpos).1.norm).trans (hzero K x β hx hregion)
  have hκ : ‖(((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0‖ ≤
      ‖mellin f 0‖*x^β*d := by
    rw [norm_mul]
    calc
      _ ≤ (Module.finrank ℚ K : ℝ)*‖mellin f 0‖ :=
        mul_le_mul_of_nonneg_right (mixedDedekindZeroOrder_norm_le_degree K) (norm_nonneg _)
      _ ≤ d*‖mellin f 0‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ ≤ x^β*d*‖mellin f 0‖ := mul_le_mul_of_nonneg_right
        (by nlinarith : d ≤ x^β*d) (norm_nonneg _)
      _ = _ := by ring
  rw [dedekindPrimePower_explicitFormula K f hcompact hpositive hsmooth hxpos]
  calc
    _ ≤ (‖(x : ℂ)*mellin f 1‖+
        ‖∑' ρ,(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ‖)+
        ‖(((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0‖+
        ‖((1/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)‖ := by
      exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ x*‖mellin f 1‖+B*x^β*d+‖mellin f 0‖*x^β*d+A*x^β*d := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos]
      exact add_le_add (add_le_add (add_le_add le_rfl hZ) hκ) hL
    _ ≤ _ := by
      change _ ≤ (‖mellin f 1‖+B+‖mellin f 0‖+A+1)*(x+x^β*d)
      nlinarith [mul_nonneg (norm_nonneg (mellin f 1)) (mul_nonneg (Real.rpow_nonneg hxpos.le β) hd),
        mul_nonneg (norm_nonneg (mellin f 0)) hxpos.le,
        mul_nonneg hA.le hxpos.le,mul_nonneg hB.le hxpos.le]

end
end ArtinMatthews.VaryingKummerAnalytic
