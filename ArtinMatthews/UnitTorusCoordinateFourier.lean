module

public import ArtinMatthews.UnitTorusWeakGradient
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


set_option backward.privateInPublic true
@[expose] public section

/-! Fourier coefficients of actual coordinate derivatives on the normalized torus. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus Set
open scoped BigOperators ComplexConjugate
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem unitTorus_update_measurePreserving (j : ι) :
    MeasurePreserving (fun p : UnitAddTorus ι × UnitAddCircle => Function.update p.1 j p.2)
      ((unitTorusHaar ι).prod AddCircle.haarAddCircle) (unitTorusHaar ι) := by
  have hmeas : Measurable (fun p : UnitAddTorus ι × UnitAddCircle => Function.update p.1 j p.2) :=
    (continuous_fst.update j continuous_snd).measurable
  refine ⟨hmeas, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : UnitAddTorus ι × UnitAddCircle => Function.update p.1 j p.2) ⁻¹'
      (Set.univ.pi s) = (Set.univ.pi (Function.update s j Set.univ)) ×ˢ s j := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro i
        by_cases hi : i = j
        · subst i
          simp
        · simpa [hi] using h i
      · simpa using h j
    · rintro ⟨hx, hy⟩ i
      by_cases hi : i = j
      · subst i
        simpa using hy
      · simpa [hi] using hx i
  rw [hpre, Measure.prod_prod, unitTorusHaar, Measure.pi_pi]
  have hfun : (fun i => AddCircle.haarAddCircle (Function.update s j Set.univ i)) =
      Function.update (fun i => AddCircle.haarAddCircle (s i)) j 1 := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j), one_mul]
  simpa only [Finset.sdiff_singleton_eq_erase] using
    (Finset.prod_erase_mul (f := fun i => AddCircle.haarAddCircle (s i))
      (Finset.univ) (Finset.mem_univ j))

theorem unitTorus_integral_update (f : C(UnitAddTorus ι, ℂ)) (j : ι) :
    (∫ x, f x ∂unitTorusHaar ι) =
      ∫ x, (∫ y, f (Function.update x j y) ∂AddCircle.haarAddCircle) ∂unitTorusHaar ι := by
  have hm := unitTorus_update_measurePreserving ι j
  have hi : Integrable (fun p : UnitAddTorus ι × UnitAddCircle => f (Function.update p.1 j p.2))
      ((unitTorusHaar ι).prod AddCircle.haarAddCircle) :=
    (f.continuous.comp (continuous_fst.update j continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ x, f x ∂Measure.map (fun p : UnitAddTorus ι × UnitAddCircle => Function.update p.1 j p.2)
        ((unitTorusHaar ι).prod AddCircle.haarAddCircle) := by rw [hm.map_eq]
    _ = ∫ p : UnitAddTorus ι × UnitAddCircle, f (Function.update p.1 j p.2)
        ∂(unitTorusHaar ι).prod AddCircle.haarAddCircle :=
      integral_map hm.measurable.aemeasurable f.continuous.aestronglyMeasurable
    _ = _ := integral_prod _ hi

omit [Fintype ι] [DecidableEq ι] in
theorem unitCircle_fourier_coordinate_derivative (f g : C(UnitAddCircle, ℂ))
    (hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => f (u : UnitAddCircle)) (g (t : UnitAddCircle)) t)
    (n : ℤ) :
    fourierCoeff g n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * fourierCoeff f n := by
  let a : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
  let W : ℝ → ℂ := fun t => fourier (-n) (t : UnitAddCircle)
  let F : ℝ → ℂ := fun t => W t * f (t : UnitAddCircle)
  let G : ℝ → ℂ := fun t => -a * (W t * f (t : UnitAddCircle)) + W t * g (t : UnitAddCircle)
  have hW (t : ℝ) : HasDerivAt W (-a * W t) t := by
    convert hasDerivAt_fourier_neg 1 n t using 1
    dsimp [W, a]
    norm_num
  have hD (t : ℝ) : HasDerivAt F (G t) t := by
    convert (hW t).mul (hd t) using 1
    dsimp [F, G]
    ring
  have hFc : Continuous W := (fourier (-n)).continuous.comp (AddCircle.continuous_mk' 1)
  have hgc : Continuous G := by
    dsimp [G]
    exact (continuous_const.mul (hFc.mul (g := fun t : ℝ => f (t : UnitAddCircle))
      (f.continuous.comp (AddCircle.continuous_mk' 1)))).add
      (hFc.mul (g.continuous.comp (AddCircle.continuous_mk' 1)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hD t) (hgc.intervalIntegrable 0 1)
  have hboundary : F 1 - F 0 = 0 := by
    have hp : ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
      rw [AddCircle.coe_period, AddCircle.coe_zero]
    change fourier (-n) ((1 : ℝ) : UnitAddCircle) * f ((1 : ℝ) : UnitAddCircle) -
      fourier (-n) ((0 : ℝ) : UnitAddCircle) * f ((0 : ℝ) : UnitAddCircle) = 0
    rw [hp, sub_self]
  have hrel : -a * (∫ t in (0 : ℝ)..1, W t * f (t : UnitAddCircle)) +
      (∫ t in (0 : ℝ)..1, W t * g (t : UnitAddCircle)) = 0 := by
    rw [hboundary] at hFTC
    change (∫ t in (0 : ℝ)..1, -a * (W t * f (t : UnitAddCircle)) +
      W t * g (t : UnitAddCircle)) = 0 at hFTC
    have hi1 : IntervalIntegrable (fun t : ℝ => -a * (W t * f (t : UnitAddCircle))) volume 0 1 :=
      (continuous_const.mul (hFc.mul (f.continuous.comp (AddCircle.continuous_mk' 1)))).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun t : ℝ => W t * g (t : UnitAddCircle)) volume 0 1 :=
      (hFc.mul (g.continuous.comp (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul] at hFTC
    exact hFTC
  rw [fourierCoeff_eq_intervalIntegral g n 0,
    fourierCoeff_eq_intervalIntegral f n 0]
  simp only [one_div_one, one_smul, zero_add]
  change (∫ t in (0 : ℝ)..1, W t * g (t : UnitAddCircle)) =
    a * (∫ t in (0 : ℝ)..1, W t * f (t : UnitAddCircle))
  linear_combination hrel

private theorem unitTorus_slice_coefficient (f : C(UnitAddTorus ι, ℂ))
    (n : ι → ℤ) (x : UnitAddTorus ι) (j : ι) :
    (∫ y, mFourier (-n) (Function.update x j y) * f (Function.update x j y)
      ∂AddCircle.haarAddCircle) =
      (∏ i ∈ Finset.univ \ {j}, fourier (-(n i)) (x i)) *
        fourierCoeff (fun y => f (Function.update x j y)) (n j) := by
  have hfactor (y : UnitAddCircle) : mFourier (-n) (Function.update x j y) =
      fourier (-(n j)) y *
        ∏ i ∈ Finset.univ \ {j}, fourier (-(n i)) (x i) := by
    change (∏ i, fourier (-(n i)) (Function.update x j y i)) = _
    have hfun : (fun i => fourier (-(n i)) (Function.update x j y i)) =
        Function.update (fun i => fourier (-(n i)) (x i)) j
          (fourier (-(n j)) y) := by
      funext i
      by_cases hi : i = j <;> simp [hi]
    rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j)]
  simp_rw [hfactor]
  change (∫ y, (fourier (-(n j)) y *
      ∏ i ∈ Finset.univ \ {j}, fourier (-(n i)) (x i)) * f (Function.update x j y)
      ∂AddCircle.haarAddCircle) =
    (∏ i ∈ Finset.univ \ {j}, fourier (-(n i)) (x i)) *
      (∫ y, fourier (-(n j)) y * f (Function.update x j y) ∂AddCircle.haarAddCircle)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change _ = _ * (fourier (-(n j)) y * f (Function.update x j y))
    ring

theorem unitTorus_fourier_coordinate_derivative
    (f : C(UnitAddTorus ι, ℂ)) (g : ι → C(UnitAddTorus ι, ℂ))
    (hd : ∀ (j : ι) (x : UnitAddTorus ι) (t : ℝ), HasDerivAt (fun u : ℝ => f (Function.update x j (u : UnitAddCircle)))
      (g j (Function.update x j (t : UnitAddCircle))) t)
    (j : ι) (n : ι → ℤ) :
    mFourierCoeff (g j) n = (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) * mFourierCoeff f n := by
  let W (h : C(UnitAddTorus ι, ℂ)) : C(UnitAddTorus ι, ℂ) := (mFourier (-n)) * h
  have hcoeff (h : C(UnitAddTorus ι, ℂ)) : mFourierCoeff h n =
      ∫ x, (∫ y, mFourier (-n) (Function.update x j y) * h (Function.update x j y)
        ∂AddCircle.haarAddCircle) ∂unitTorusHaar ι := by
    change (∫ x, W h x ∂unitTorusHaar ι) = _
    exact unitTorus_integral_update ι (W h) j
  rw [hcoeff (g j), hcoeff f, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change (∫ y, mFourier (-n) (Function.update x j y) * g j (Function.update x j y)
      ∂AddCircle.haarAddCircle) =
    (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
      (∫ y, mFourier (-n) (Function.update x j y) * f (Function.update x j y)
        ∂AddCircle.haarAddCircle)
  rw [unitTorus_slice_coefficient ι (g j) n x j, unitTorus_slice_coefficient ι f n x j]
  let fx : C(UnitAddCircle, ℂ) := ⟨fun y => f (Function.update x j y),
    f.continuous.comp (continuous_const.update j continuous_id)⟩
  let gx : C(UnitAddCircle, ℂ) := ⟨fun y => g j (Function.update x j y),
    (g j).continuous.comp (continuous_const.update j continuous_id)⟩
  have h := unitCircle_fourier_coordinate_derivative fx gx (hd j x) (n j)
  change fourierCoeff (fun y => g j (Function.update x j y)) (n j) =
    (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
      fourierCoeff (fun y => f (Function.update x j y)) (n j) at h
  rw [h]
  ring

theorem unitTorusWeakGradient_of_coordinate_derivative
    (f : C(UnitAddTorus ι, ℂ)) (g : ι → C(UnitAddTorus ι, ℂ))
    (hd : ∀ (j : ι) (x : UnitAddTorus ι) (t : ℝ), HasDerivAt (fun u : ℝ => f (Function.update x j (u : UnitAddCircle)))
      (g j (Function.update x j (t : UnitAddCircle))) t) :
    UnitTorusWeakGradient ι (f.toLp 2 (unitTorusHaar ι) ℂ)
      (fun j => (g j).toLp 2 (unitTorusHaar ι) ℂ) := by
  intro j n
  rw [show mFourierCoeff ((g j).toLp 2 (unitTorusHaar ι) ℂ) n = mFourierCoeff (g j) n from
      mFourierCoeff_toLp (g j) n,
    show mFourierCoeff (f.toLp 2 (unitTorusHaar ι) ℂ) n = mFourierCoeff f n from
      mFourierCoeff_toLp f n]
  exact unitTorus_fourier_coordinate_derivative ι f g hd j n

end
end ArtinMatthews
