module

public import ArtinMatthews.SourceKPDeepLowerMatrix
public import ArtinMatthews.StandardLocalHaarScaling


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine deep ideal has compact-open image in the local field.
Its standard self-dual Haar volume and the integral of its indicator
are finite and strictly positive. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain IsLocalRing MeasureTheory StandardAdelic SourcePhysical Set
open scoped NumberField SourcePhysical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local notation "O" => P.adicCompletionIntegers K
local notation "L" => P.adicCompletion K
local notation "J₀" => sourceKPDeepIdeal K P
local notation "S₀" => sourceKPDeepIdealImage K P
local notation "μ₀" => sourceLocalSelfDual K P

theorem sourceKPDeepIdealImage_eq_scaled_integer :
    ∃ a : L, a ≠ 0 ∧ S₀ = (fun x : L => a * x) '' (O : Set L) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let n := sixthLocalHenselDepth P
  let a : L := algebraMap O L (π ^ n)
  have hJ : J₀ = Ideal.span {π ^ n} := by
    rw [sourceKPDeepIdeal, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  refine ⟨a, ?_, ?_⟩
  · intro h
    apply pow_ne_zero n hπ.ne_zero
    exact Subtype.ext h
  · ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [hJ] at hr
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hr
      refine ⟨(b : L), b.property, ?_⟩
      change algebraMap O L (π ^ n) * algebraMap O L b = algebraMap O L r
      rw [← map_mul]
      exact (congrArg (algebraMap O L) hb).symm
    · rintro ⟨y, hy, rfl⟩
      let b : O := ⟨y, hy⟩
      refine ⟨π ^ n * b, ?_, ?_⟩
      · rw [hJ]
        exact Ideal.mem_span_singleton.mpr ⟨b, rfl⟩
      · change algebraMap O L (π ^ n * b) = a * y
        rw [map_mul]
        rfl

theorem sourceKPDeepIdealImage_isOpen : IsOpen S₀ := by
  obtain ⟨a, ha, he⟩ := sourceKPDeepIdealImage_eq_scaled_integer K P
  rw [he]
  apply (Homeomorph.mulLeft₀ a ha).isOpenMap
  rw [← sourceLocalBall_zero K P]
  exact sourceLocalBall_isOpen K P 0

theorem sourceKPDeepIdealImage_isCompact : IsCompact S₀ := by
  obtain ⟨a, _, he⟩ := sourceKPDeepIdealImage_eq_scaled_integer K P
  rw [he, ← sourceLocalBall_zero K P]
  exact (sourceLocalBall_isCompact K P 0).image (continuous_const.mul continuous_id)

theorem sourceKPDeepIdealImage_zero : (0 : L) ∈ S₀ :=
  ⟨0, (J₀).zero_mem, map_zero _⟩

theorem sourceKPDeepIdealImage_volume_ne_top : μ₀ S₀ ≠ ∞ := by
  let : (μ₀).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  exact (sourceKPDeepIdealImage_isCompact K P).measure_ne_top

theorem sourceKPDeepIdealImage_volume_pos : 0 < (μ₀).real S₀ := by
  let : (μ₀).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have hp : 0 < μ₀ S₀ := (sourceKPDeepIdealImage_isOpen K P).measure_pos μ₀
    ⟨0, sourceKPDeepIdealImage_zero K P⟩
  exact ENNReal.toReal_pos hp.ne' (sourceKPDeepIdealImage_volume_ne_top K P)

def sourceKPDeepIdealIndicator (x : L) : ℂ := (S₀).indicator (fun _ => 1) x

theorem sourceKPDeepIdealIndicator_integrable : Integrable (sourceKPDeepIdealIndicator K P) μ₀ := by
  unfold sourceKPDeepIdealIndicator
  rw [integrable_indicator_iff (sourceKPDeepIdealImage_isOpen K P).measurableSet]
  exact integrableOn_const (sourceKPDeepIdealImage_volume_ne_top K P)

theorem sourceKPDeepIdealIndicator_integral :
    (∫ x, sourceKPDeepIdealIndicator K P x ∂μ₀) = ((μ₀).real S₀ : ℂ) := by
  unfold sourceKPDeepIdealIndicator
  rw [integral_indicator (sourceKPDeepIdealImage_isOpen K P).measurableSet]
  simp only [integral_const, Measure.restrict_apply_univ, Complex.real_smul, mul_one, Measure.real]

theorem sourceKPDeepIdealIndicator_integral_ne_zero :
    (∫ x, sourceKPDeepIdealIndicator K P x ∂μ₀) ≠ 0 := by
  rw [sourceKPDeepIdealIndicator_integral]
  exact Complex.ofReal_ne_zero.mpr (sourceKPDeepIdealImage_volume_pos K P).ne'

end
end ArtinMatthews
