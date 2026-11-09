module

public import ArtinMatthews.VaryingKummerAnalyticMixedPositiveMellin
public import ArtinMatthews.VaryingKummerAnalyticMixedThetaPositive


set_option backward.privateInPublic true
@[expose] public section

/-! The actual mixed-signature unit-averaged theta Mellin integral equals the
positive partial Dedekind ideal series, with its exact Gamma and torsion factors.
The general-field norm identities are exact OpenAI source extracts. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
lemma fractionalIdeal_absNorm_pos {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I.1)
    (fun h => I.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.mp h.symm))

lemma idealElementRepresentative_absNorm {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (J : integralIdealClassFiber I) :
    |(Algebra.norm ℚ (idealElementRepresentative I J).1.1 : ℝ)| =
      (FractionalIdeal.absNorm I.val : ℝ) * (FractionalIdeal.absNorm J.1.val : ℝ) := by
  have h := congrArg Subtype.val (idealElementRepresentative_spec I J)
  change relativeElementIdeal I (idealElementRepresentative I J).1 = J.val at h
  have hm : J.val*I = toPrincipalIdeal (𝓞 K) K (idealElementRepresentative I J).1 := by
    rw [← h]
    simp [relativeElementIdeal]
  have hn := congrArg (fun U : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
    (FractionalIdeal.absNorm U.val : ℝ)) hm
  simp only [Units.val_mul, map_mul, coe_toPrincipalIdeal,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs] at hn
  rw [mul_comm] at hn
  exact hn.symm


variable (K : Type*) [Field K] [NumberField K]

def mixedRealHeckeFactor (s : ℝ) : ℝ := mixedRadialJacobian K * mixedRealGammaFactor K s

theorem mixedRealHeckeFactor_pos {s : ℝ} (hs : 0 < s) : 0 < mixedRealHeckeFactor K s :=
  mul_pos (mixedRadialJacobian_pos K) (mixedRealGammaFactor_pos K hs)

theorem mixedArchGaussian_joint_measurable (a : K) :
    Measurable (fun p : ℝ × logSpace K => mixedArchGaussian K a p.1 p.2) := by
  change Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal
    (Real.exp (-Real.pi*p.1*mixedArchEnergy K a p.2)))
  have he := mixedArchEnergy_continuous K a
  fun_prop

/-- Positive partial Dedekind series over genuine nonzero integral ideals in the
inverse ideal class of `I`. The ENNReal formulation also allows divergent parameters. -/
def mixedPartialDedekindPositive (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℝ) : ℝ≥0∞ :=
  ∑' J : integralIdealClassFiber I, ENNReal.ofReal ((FractionalIdeal.absNorm J.1.1 : ℝ)^(-s))

theorem mixedIdealPositiveTheta_mellin (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((Module.finrank ℚ K : ℝ)*s/2-1)) *
      ∫⁻ u in mixedUnitLogDomain K, mixedIdealPositiveThetaTail K I u t) =
      (torsionOrder K : ℝ≥0∞) *
        ENNReal.ofReal (mixedRealHeckeFactor K s * (FractionalIdeal.absNorm I.1 : ℝ)^(-s)) *
        mixedPartialDedekindPositive K I s := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  let H (J : integralIdealClassFiber I) (t : ℝ) : ℝ≥0∞ :=
    ENNReal.ofReal (t^((Module.finrank ℚ K : ℝ)*s/2-1)) *
      ∫⁻ u, mixedArchGaussian K (idealElementRepresentative I J).1.1 t u
  have hm (J : integralIdealClassFiber I) : Measurable (H J) := by
    apply Measurable.mul (by fun_prop)
    exact (mixedArchGaussian_joint_measurable K _).lintegral_prod_right'
  have he : (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((Module.finrank ℚ K : ℝ)*s/2-1)) *
      ∫⁻ u in mixedUnitLogDomain K, mixedIdealPositiveThetaTail K I u t) =
      ∫⁻ t in Ioi 0, (torsionOrder K : ℝ≥0∞) * ∑' J, H J t := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [mixedIdealPositiveThetaTail_unit_unfold K I t,
      mul_left_comm, ← ENNReal.tsum_mul_left]
  rw [he, lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
    lintegral_tsum (fun J => (hm J).aemeasurable)]
  have hj (J : integralIdealClassFiber I) :
      (∫⁻ t in Ioi 0, H J t) =
        ENNReal.ofReal (mixedRealHeckeFactor K s * (FractionalIdeal.absNorm I.1 : ℝ)^(-s)) *
          ENNReal.ofReal ((FractionalIdeal.absNorm J.1.1 : ℝ)^(-s)) := by
    dsimp only [H]
    rw [mixedArchGaussian_mellin_lintegral K (idealElementRepresentative I J).1.ne_zero hs,
      idealElementRepresentative_absNorm,
      Real.mul_rpow (fractionalIdeal_absNorm_pos I).le (fractionalIdeal_absNorm_pos J.1).le]
    change ENNReal.ofReal (mixedRealHeckeFactor K s * (_ * _)) = _
    rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg (mixedRealHeckeFactor_pos K hs).le
      (Real.rpow_nonneg (fractionalIdeal_absNorm_pos I).le _))]
  simp_rw [hj]
  rw [ENNReal.tsum_mul_left, mul_assoc]
  rfl

/-- The same identity for the previously constructed actual complex theta family. -/
theorem mixedIdealFlowTheta_mellin_positive (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^((Module.finrank ℚ K : ℝ)*s/2-1)) *
      ∫⁻ u in mixedUnitLogDomain K, ENNReal.ofReal ((mixedIdealFlowTheta K I u t - 1).re)) =
      (torsionOrder K : ℝ≥0∞) *
        ENNReal.ofReal (mixedRealHeckeFactor K s * (FractionalIdeal.absNorm I.1 : ℝ)^(-s)) *
        mixedPartialDedekindPositive K I s := by
  rw [← mixedIdealPositiveTheta_mellin K I hs]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  simp_rw [mixedIdealFlowTheta_real_nonzero K I _ ht]

end
end ArtinMatthews.VaryingKummerAnalytic
