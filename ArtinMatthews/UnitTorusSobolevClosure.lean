module

public import ArtinMatthews.UnitTorusCoordinateFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Actual trigonometric derivatives are a core for the closed multitorus gradient. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus
open scoped BigOperators ComplexConjugate Topology
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem unitTorus_mFourier_hasDerivAt (n : ι → ℤ) (j : ι) (x : UnitAddTorus ι) (t : ℝ) :
    HasDerivAt (fun u : ℝ => mFourier n (Function.update x j (u : UnitAddCircle)))
      ((2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
        mFourier n (Function.update x j (t : UnitAddCircle))) t := by
  let C := ∏ i ∈ Finset.univ \ {j}, fourier (n i) (x i)
  have hf (z : UnitAddCircle) : mFourier n (Function.update x j z) = fourier (n j) z * C := by
    change (∏ i, fourier (n i) (Function.update x j z i)) = _
    have hfun : (fun i => fourier (n i) (Function.update x j z i)) =
        Function.update (fun i => fourier (n i) (x i)) j (fourier (n j) z) := by
      funext i
      by_cases hi : i = j <;> simp [hi]
    rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j)]
  have h := (hasDerivAt_fourier 1 (n j) t).mul_const C
  convert h using 1
  · funext u
    exact hf _
  · rw [hf]
    norm_num
    ring

def unitTorusPolynomial (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) : C(UnitAddTorus ι, ℂ) :=
  ∑ n ∈ S, a n • mFourier n

def unitTorusPolynomialDerivative (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ)
    (j : ι) : C(UnitAddTorus ι, ℂ) :=
  ∑ n ∈ S, ((2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) * a n) • mFourier n

theorem unitTorusPolynomial_hasDerivAt (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ)
    (j : ι) (x : UnitAddTorus ι) (t : ℝ) :
    HasDerivAt (fun u : ℝ => unitTorusPolynomial ι S a (Function.update x j (u : UnitAddCircle)))
      (unitTorusPolynomialDerivative ι S a j (Function.update x j (t : UnitAddCircle))) t := by
  have h := HasDerivAt.fun_sum (u := S) (fun n _ =>
    (unitTorus_mFourier_hasDerivAt ι n j x t).const_mul (a n))
  simpa [unitTorusPolynomial, unitTorusPolynomialDerivative, smul_eq_mul,
    mul_assoc, mul_comm, mul_left_comm] using h

def unitTorusPolynomialPair (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) :
    UnitTorusL2 ι × (ι → UnitTorusL2 ι) :=
  ((unitTorusPolynomial ι S a).toLp 2 (unitTorusHaar ι) ℂ,
    fun j => (unitTorusPolynomialDerivative ι S a j).toLp 2 (unitTorusHaar ι) ℂ)

theorem unitTorusPolynomialPair_weak (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) :
    UnitTorusWeakGradient ι (unitTorusPolynomialPair ι S a).1 (unitTorusPolynomialPair ι S a).2 :=
  unitTorusWeakGradient_of_coordinate_derivative ι _ _
    (unitTorusPolynomial_hasDerivAt ι S a)

omit [DecidableEq ι] in
theorem unitTorusPolynomial_toLp (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) :
    (unitTorusPolynomial ι S a).toLp 2 (unitTorusHaar ι) ℂ =
      ∑ n ∈ S, a n • mFourierBasis n := by
  simp only [unitTorusPolynomial, map_sum, map_smul, coe_mFourierBasis]
  rfl

omit [DecidableEq ι] in
theorem unitTorusPolynomialDerivative_toLp (S : Finset (ι → ℤ)) (a : (ι → ℤ) → ℂ) (j : ι) :
    (unitTorusPolynomialDerivative ι S a j).toLp 2 (unitTorusHaar ι) ℂ =
      ∑ n ∈ S, ((2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) * a n) • mFourierBasis n := by
  simp only [unitTorusPolynomialDerivative, map_sum, map_smul, coe_mFourierBasis]
  rfl

omit [DecidableEq ι] in
theorem unitTorusPolynomialPair_tendsto (f : UnitTorusL2 ι) (g : ι → UnitTorusL2 ι)
    (hgrad : UnitTorusWeakGradient ι f g) :
    Filter.Tendsto (fun S : Finset (ι → ℤ) =>
      unitTorusPolynomialPair ι S (mFourierCoeff f)) Filter.atTop (𝓝 (f, g)) := by
  have hf : Filter.Tendsto (fun S : Finset (ι → ℤ) =>
      (unitTorusPolynomialPair ι S (mFourierCoeff f)).1) Filter.atTop (𝓝 f) := by
    simpa only [unitTorusPolynomialPair, unitTorusPolynomial_toLp, coe_mFourierBasis,
      HasSum, SummationFilter.unconditional_filter] using
      hasSum_mFourier_series_L2 f
  have hg : Filter.Tendsto (fun S : Finset (ι → ℤ) =>
      (unitTorusPolynomialPair ι S (mFourierCoeff f)).2) Filter.atTop (𝓝 g) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have h := hasSum_mFourier_series_L2 (g j)
    simp only [hgrad j] at h
    simpa only [unitTorusPolynomialPair, unitTorusPolynomialDerivative_toLp, coe_mFourierBasis,
      HasSum, SummationFilter.unconditional_filter] using h
  exact hf.prodMk_nhds hg

theorem unitTorusPolynomialGraph_closure :
    closure (Set.range (fun p : Finset (ι → ℤ) × ((ι → ℤ) → ℂ) =>
      unitTorusPolynomialPair ι p.1 p.2)) =
      {fg : UnitTorusL2 ι × (ι → UnitTorusL2 ι) | UnitTorusWeakGradient ι fg.1 fg.2} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro fg ⟨⟨S, a⟩, rfl⟩
      exact unitTorusPolynomialPair_weak ι S a
    · exact unitTorusWeakGradient_isClosed ι
  · rintro ⟨f, g⟩ hgrad
    exact mem_closure_of_tendsto (unitTorusPolynomialPair_tendsto ι f g hgrad)
      (Filter.Eventually.of_forall fun S => ⟨(S, mFourierCoeff f), rfl⟩)

abbrev UnitTorusH1 :=
  {fg : UnitTorusL2 ι × (ι → UnitTorusL2 ι) // UnitTorusWeakGradient ι fg.1 fg.2}

instance unitTorusH1_complete : CompleteSpace (UnitTorusH1 ι) :=
  (unitTorusWeakGradient_isClosed ι).isComplete.completeSpace_coe

end
end ArtinMatthews
