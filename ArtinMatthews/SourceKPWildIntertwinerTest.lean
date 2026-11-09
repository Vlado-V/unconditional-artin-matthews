module

public import ArtinMatthews.SourceKPWildCompactSupport
public import ArtinMatthews.SourceKPDeepIdealHaar
public import ArtinMatthews.SourceKPWeylLower


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine nonzero ramified scalar intertwining test for the
constructed full adelic compact section. Its integrand is exactly
the indicator of the actual deep ideal, for every parameter. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hP : (6 : 𝓞 K) ∈ P.asIdeal)

local notation "L" => P.adicCompletion K
local notation "μ₀" => sourceLocalSelfDual K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "j₀" => sourceKPAdelicLocalProjective K hζ P

include hP in
theorem sourceKPAdelicCompactScalar_lower_indicator (s : ℂ) (x : L) :
    sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicLowerAt K hζ P x) =
      sourceKPDeepIdealIndicator K P x := by
  classical
  unfold sourceKPDeepIdealIndicator
  by_cases hx : x ∈ sourceKPDeepIdealImage K P
  · rw [Set.indicator_of_mem hx]
    exact sourceKPAdelicCompactScalar_lower_mem K hζ P s hx
  · rw [Set.indicator_of_notMem hx]
    exact sourceKPAdelicCompactScalar_zero K hζ s _
      (fun h => hx ((sourceKPAdelicLowerAt_factorable_iff K hζ P hP x).mp h))

def sourceKPWildIntertwinerKernel (s : ℂ) (x : L) : ℂ :=
  sourceKPAdelicCompactScalar K hζ s
    (j₀ (l₀ sourceGL2Weyl) * j₀ (l₀ (sourceGL2Upper x)) * j₀ (l₀ sourceGL2Weyl))

include hP in
theorem sourceKPWildIntertwinerKernel_eq_indicator (s : ℂ) (x : L) :
    sourceKPWildIntertwinerKernel K hζ P s x = sourceKPDeepIdealIndicator K P x := by
  unfold sourceKPWildIntertwinerKernel
  rw [sourceKPAdelicLocalProjective_weyl_upper_weyl]
  exact sourceKPAdelicCompactScalar_lower_indicator K hζ P hP s x

include hP in
theorem sourceKPWildIntertwinerKernel_integrable (s : ℂ) :
    Integrable (sourceKPWildIntertwinerKernel K hζ P s) μ₀ := by
  have he : sourceKPWildIntertwinerKernel K hζ P s = sourceKPDeepIdealIndicator K P :=
    funext (sourceKPWildIntertwinerKernel_eq_indicator K hζ P hP s)
  rw [he]
  exact sourceKPDeepIdealIndicator_integrable K P

include hP in
theorem sourceKPWildIntertwinerKernel_integral (s : ℂ) :
    (∫ x, sourceKPWildIntertwinerKernel K hζ P s x ∂μ₀) =
      ((sourceLocalSelfDual K P).real (sourceKPDeepIdealImage K P) : ℂ) := by
  have he : sourceKPWildIntertwinerKernel K hζ P s = sourceKPDeepIdealIndicator K P :=
    funext (sourceKPWildIntertwinerKernel_eq_indicator K hζ P hP s)
  rw [he]
  exact sourceKPDeepIdealIndicator_integral K P

include hP in
theorem sourceKPWildIntertwinerKernel_integral_ne_zero (s : ℂ) :
    (∫ x, sourceKPWildIntertwinerKernel K hζ P s x ∂μ₀) ≠ 0 := by
  rw [sourceKPWildIntertwinerKernel_integral K hζ P hP s]
  exact Complex.ofReal_ne_zero.mpr (sourceKPDeepIdealImage_volume_pos K P).ne'

include hP in
theorem sourceKPWildIntertwinerKernel_integral_entire :
    Differentiable ℂ (fun s : ℂ => ∫ x, sourceKPWildIntertwinerKernel K hζ P s x ∂μ₀) := by
  simp_rw [sourceKPWildIntertwinerKernel_integral K hζ P hP]
  exact differentiable_const _

end
end ArtinMatthews
