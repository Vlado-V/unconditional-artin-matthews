module

public import ArtinMatthews.UnitTorusFourierTail


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite linear combinations of coordinate weak derivatives. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus
open scoped BigOperators ComplexConjugate ENNReal
noncomputable section

local instance unitTorusDerivativeCombinationCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance unitTorusDerivativeCombinationCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (ι : Type*) [Fintype ι]

def unitTorusDerivativeCombination (g : ι → UnitTorusL2 ι) (c : ι → ℝ) : UnitTorusL2 ι :=
  ∑ i, (c i : ℂ) • g i

theorem unitTorusDerivativeCombination_fourier (f : UnitTorusL2 ι) (g : ι → UnitTorusL2 ι)
    (hg : UnitTorusWeakGradient ι f g) (c : ι → ℝ) (n : ι → ℤ) :
    mFourierCoeff (unitTorusDerivativeCombination ι g c) n =
      (2 * (Real.pi : ℂ) * Complex.I * ((∑ i, c i * (n i : ℝ) : ℝ) : ℂ)) * mFourierCoeff f n := by
  change ∀ i n, mFourierCoeff (g i) n =
    (2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ)) * mFourierCoeff f n at hg
  rw [← unitTorusCoefficient_apply]
  simp only [unitTorusDerivativeCombination, map_sum, map_smul, unitTorusCoefficient_apply, hg,
    smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end ArtinMatthews
