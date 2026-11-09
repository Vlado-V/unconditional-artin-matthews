module

public import ArtinMatthews.SourceSLocalRadialHomeomorph
public import ArtinMatthews.SLocalPositiveScaling
public import Mathlib.MeasureTheory.Group.Integral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField Classical ENNReal
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- Equal-norm sections differ by a literal element of the actual norm-one subgroup. -/
def sourceSLocalSameNormRatio (u v : SWholeUnits K S)
    (h : sLocalNorm K S u = sLocalNorm K S v) : SNormOne K S :=
  ⟨u * v⁻¹, by
    change sLocalNorm K S (u * v⁻¹) = 1
    rw [sLocalNorm_mul, sLocalNorm_inv, h]
    exact mul_inv_cancel₀ (sLocalNorm_pos K S v).ne'⟩

theorem sourceSLocalSameNormRatio_mul (u v : SWholeUnits K S)
    (h : sLocalNorm K S u = sLocalNorm K S v) :
    (sourceSLocalSameNormRatio S u v h : SWholeUnits K S) * v = u :=
  inv_mul_cancel_right _ _

theorem sourceSLocal_sameNorm_lintegral (ν : Measure (SNormOne K S))
    [ν.IsHaarMeasure] (F : SWholeUnits K S → ℝ≥0∞)
    (u v : SWholeUnits K S) (h : sLocalNorm K S u = sLocalNorm K S v) :
    (∫⁻ x : SNormOne K S, F ((x : SWholeUnits K S) * u) ∂ν) =
      ∫⁻ x : SNormOne K S, F ((x : SWholeUnits K S) * v) ∂ν := by
  let k := sourceSLocalSameNormRatio S u v h
  have hk : (k : SWholeUnits K S) * v = u := sourceSLocalSameNormRatio_mul S u v h
  calc
    _ = ∫⁻ x : SNormOne K S, F (((k * x : SNormOne K S) : SWholeUnits K S) * v) ∂ν := by
      apply lintegral_congr
      intro x
      change F ((x : SWholeUnits K S) * u) =
        F (((k : SWholeUnits K S) * (x : SWholeUnits K S)) * v)
      rw [← hk, mul_comm (k : SWholeUnits K S) (x : SWholeUnits K S), mul_assoc]
    _ = _ := lintegral_mul_left_eq_self (fun x : SNormOne K S => F ((x : SWholeUnits K S) * v)) k

theorem sourceSLocal_sameNorm_integral (ν : Measure (SNormOne K S))
    [ν.IsHaarMeasure] (F : SWholeUnits K S → ℂ)
    (u v : SWholeUnits K S) (h : sLocalNorm K S u = sLocalNorm K S v) :
    (∫ x : SNormOne K S, F ((x : SWholeUnits K S) * u) ∂ν) =
      ∫ x : SNormOne K S, F ((x : SWholeUnits K S) * v) ∂ν := by
  let k := sourceSLocalSameNormRatio S u v h
  have hk : (k : SWholeUnits K S) * v = u := sourceSLocalSameNormRatio_mul S u v h
  calc
    _ = ∫ x : SNormOne K S, F (((k * x : SNormOne K S) : SWholeUnits K S) * v) ∂ν := by
      apply integral_congr_ae
      filter_upwards with x
      change F ((x : SWholeUnits K S) * u) =
        F (((k : SWholeUnits K S) * (x : SWholeUnits K S)) * v)
      rw [← hk, mul_comm (k : SWholeUnits K S) (x : SWholeUnits K S), mul_assoc]
    _ = _ := integral_mul_left_eq_self (fun x : SNormOne K S => F ((x : SWholeUnits K S) * v)) k

/-- The paper's all-place dilation ell_T gives the same actual sheet integral
as the single-place section used for the change of variables. -/
theorem sourceSLocal_radial_integral_eq_literal (ν : Measure (SNormOne K S))
    [ν.IsHaarMeasure] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    {v : InfinitePlace K} (hv : IsComplex v) (F : SWholeUnits K S → ℂ)
    (t : ℝ) :
    (∫ x : SNormOne K S, F ((x : SWholeUnits K S) * sourceSLocalRadial hv S t) ∂ν) =
      ∫ x : SNormOne K S, F ((x : SWholeUnits K S) *
        sLocalPositiveScaling K hζ S (Real.exp t)) ∂ν := by
  apply sourceSLocal_sameNorm_integral S ν F
  rw [sourceSLocalRadial_norm, sLocalPositiveScaling_norm K hζ S (Real.exp_pos _)]

end
end ArtinMatthews.SourcePhysical
