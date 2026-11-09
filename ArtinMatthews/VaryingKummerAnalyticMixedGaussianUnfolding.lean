module

public import ArtinMatthews.VaryingKummerAnalyticUnitUnfolding
public import ArtinMatthews.VaryingKummerAnalyticIdealOrbits


set_option backward.privateInPublic true
@[expose] public section

/-! Actual archimedean Gaussian and unit-orbit unfolding in arbitrary signature.
Complex places receive the required half-log scaling. No totally-real hypothesis
or fixed roots-of-unity count occurs. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem mixedRestoredPlaceLog_add (u v : logSpace K) (w : InfinitePlace K) :
    mixedRestoredPlaceLog K (u + v) w =
      mixedRestoredPlaceLog K u w + mixedRestoredPlaceLog K v w := by
  unfold mixedRestoredPlaceLog
  split_ifs <;> simp [Finset.sum_add_distrib, neg_add_rev, add_comm]

def mixedPlaceWeight (u : logSpace K) (w : InfinitePlace K) : ℝ :=
  Real.exp (mixedRestoredPlaceLog K u w / InfinitePlace.mult w)

theorem mixedPlaceWeight_continuous (w : InfinitePlace K) :
    Continuous (fun u => mixedPlaceWeight K u w) :=
  ((mixedRestoredPlaceLog_continuous K w).div_const _).rexp

theorem mixedPlaceWeight_add (u v : logSpace K) (w : InfinitePlace K) :
    mixedPlaceWeight K (u + v) w = mixedPlaceWeight K u w * mixedPlaceWeight K v w := by
  simp only [mixedPlaceWeight, mixedRestoredPlaceLog_add, add_div, Real.exp_add]

theorem mixedPlaceWeight_unit (z : (𝓞 K)ˣ) (w : InfinitePlace K) :
    mixedPlaceWeight K (logEmbedding K (Additive.ofMul z)) w = w (z : K) := by
  rw [mixedPlaceWeight, mixedRestoredPlaceLog_unit, mul_div_cancel_left₀]
  · exact Real.exp_log (Units.pos_at_place z w)
  · exact InfinitePlace.mult_coe_ne_zero

def mixedArchGaussian (a : K) (t : ℝ) (u : logSpace K) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-Real.pi * t *
    ∑ w : InfinitePlace K, (mixedPlaceWeight K u w * w a)^2))

theorem mixedArchGaussian_measurable (a : K) (t : ℝ) :
    Measurable (mixedArchGaussian K a t) := by
  apply Measurable.ennreal_ofReal
  exact ((continuous_const.mul (continuous_finsetSum _ (fun w _ =>
    ((mixedPlaceWeight_continuous K w).mul_const _).pow 2))).rexp).measurable

theorem mixedArchGaussian_unit_translate (a : K) (z : (𝓞 K)ˣ) (t : ℝ)
    (u : logSpace K) :
    mixedArchGaussian K ((z : K) * a) t u =
      mixedArchGaussian K a t (logEmbedding K (Additive.ofMul z) + u) := by
  unfold mixedArchGaussian
  simp only [map_mul, mixedPlaceWeight_add, mixedPlaceWeight_unit]
  congr 3
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem mixedArchGaussian_units_unfold (a : K) (t : ℝ) :
    (∫⁻ u in mixedUnitLogDomain K, ∑' z : (𝓞 K)ˣ,
      mixedArchGaussian K ((z : K) * a) t u) =
      (torsionOrder K : ℝ≥0∞) * ∫⁻ u, mixedArchGaussian K a t u := by
  simp_rw [mixedArchGaussian_unit_translate]
  exact mixedUnitLog_unfold K _ (mixedArchGaussian_measurable K a t)

/-- Genuine unfolding over integral ideals in the inverse ideal class. -/
theorem mixedArchGaussian_ideal_unfold
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) :
    (∫⁻ u in mixedUnitLogDomain K, ∑' a : nonzeroIdealElements I,
      mixedArchGaussian K a.1.1 t u) =
      (torsionOrder K : ℝ≥0∞) * ∑' J : integralIdealClassFiber I,
        ∫⁻ u, mixedArchGaussian K (idealElementRepresentative I J).1.1 t u := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := NumberField.RingOfIntegers.coe_injective.countable
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  have he (u : logSpace K) :
      (∑' a : nonzeroIdealElements I, mixedArchGaussian K a.1.1 t u) =
      ∑' J : integralIdealClassFiber I, ∑' z : (𝓞 K)ˣ,
        mixedArchGaussian K ((z : K) * (idealElementRepresentative I J).1.1) t u := by
    simpa only [one_mul] using tsum_relativeElementIdeal I (fun _ => 1)
      (fun a => mixedArchGaussian K a t u)
  simp_rw [he]
  rw [lintegral_tsum (fun J => (Measurable.tsum (fun z : (𝓞 K)ˣ =>
    mixedArchGaussian_measurable K ((z : K) * (idealElementRepresentative I J).1.1) t)).aemeasurable)]
  simp_rw [mixedArchGaussian_units_unfold]
  exact ENNReal.tsum_mul_left

end
end ArtinMatthews.VaryingKummerAnalytic
