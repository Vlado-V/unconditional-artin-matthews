module

public import ArtinMatthews.SourceSLocalQuotientReflection
public import ArtinMatthews.SourceThetaProfileSmoothing


set_option backward.privateInPublic true
@[expose] public section

/-! Sixth-invariant functions integrate on the actual quotient sheet.
Signed reflection transports the descended function before Gaussian smoothing. -/
namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain MeasureTheory SourceReflection
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "N" => SNormOne K S
local notation "Q" => SNormOneSixthQuotient K S
local notation "U" => SWholeUnits K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "qmk" => sNormOneSixthQuotientMap K S

def sourceSLocalSixthInvariant (F : U → ℂ) : Prop :=
  ∀ (x : U) (γ : Γ), F (x * (γ.val : U)) = F x

theorem sourceSLocalSixthInvariant_comp_reflection (F : U → ℂ) (a : U)
    (hF : sourceSLocalSixthInvariant S F) :
    sourceSLocalSixthInvariant S (fun x => F (a * x⁻¹)) := by
  intro x γ
  change F (a * (x * (γ.val : U))⁻¹) = F (a * x⁻¹)
  rw [mul_inv_rev]
  have h := hF (a * x⁻¹) γ⁻¹
  change F ((a * x⁻¹) * (γ.val : U)⁻¹) = F (a * x⁻¹) at h
  rw [← h]
  congr 1
  ac_rfl

theorem sourceSLocalSixthInvariant_of_signed_reflection (F G : U → ℂ) (a : U)
    (ρ : ℂ) (hρ : ρ ≠ 0) (hF : sourceSLocalSixthInvariant S F)
    (heq : ∀ x, F x = ρ * G (a * x⁻¹)) : sourceSLocalSixthInvariant S G := by
  have h (x : U) : F (a * x⁻¹) = ρ * G x := by
    rw [heq (a * x⁻¹), mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
  intro x γ
  apply mul_left_cancel₀ hρ
  simpa only [h] using sourceSLocalSixthInvariant_comp_reflection S F a hF x γ

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "sc" => sLocalPositiveScaling K hζ S

def sourceSLocalQuotientSheetFunction (F : U → ℂ) (hF : sourceSLocalSixthInvariant S F)
    (T : ℝ) : Q → ℂ :=
  Quotient.lift (fun n : N => F ((n : U) * sc T)) (by
    intro x y hxy
    have hq : (y : Q) = (x : Q) := (Quotient.sound hxy).symm
    let γ : Γ := ⟨y / x, QuotientGroup.eq_iff_div_mem.mp hq⟩
    have hγ : x * γ.val = y := by
      change x * (y / x) = y
      rw [mul_comm, div_mul_cancel]
    rw [← hγ]
    change F ((x : U) * sc T) = F (((x : U) * (γ.val : U)) * sc T)
    rw [mul_assoc, mul_comm (γ.val : U) (sc T), ← mul_assoc, hF])

@[simp] theorem sourceSLocalQuotientSheetFunction_mk (F : U → ℂ)
    (hF : sourceSLocalSixthInvariant S F) (T : ℝ) (n : N) :
    sourceSLocalQuotientSheetFunction S hζ F hF T (qmk n) = F ((n : U) * sc T) := rfl

theorem sourceSLocalQuotientSheetFunction_measurable (F : U → ℂ)
    (hF : sourceSLocalSixthInvariant S F) (T : ℝ)
    (hm : Measurable (fun n : N => F ((n : U) * sc T))) :
    Measurable (sourceSLocalQuotientSheetFunction S hζ F hF T) :=
  measurable_from_quotient.mpr hm

def sourceSLocalQuotientSheetProfile (ν : Measure N) (F : U → ℂ)
    (hF : sourceSLocalSixthInvariant S F) (T : ℝ) : ℂ :=
  ∫ q, sourceSLocalQuotientSheetFunction S hζ F hF T q ∂sNormOneQuotientMeasure K S ν

theorem sourceSLocalQuotientSheetFunction_reflection (F G : U → ℂ)
    (hF : sourceSLocalSixthInvariant S F) (hG : sourceSLocalSixthInvariant S G)
    (a : U) (ρ : ℂ) (heq : ∀ x, F x = ρ * G (a * x⁻¹)) {T : ℝ} (hT : 0 < T) (q : Q) :
    sourceSLocalQuotientSheetFunction S hζ F hF T q =
      ρ * sourceSLocalQuotientSheetFunction S hζ G hG (sLocalNorm K S a / T)
        (sourceSLocalQuotientReflection S hζ a hT q) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  change sourceSLocalQuotientSheetFunction S hζ F hF T (qmk n) = _
  rw [show (n : Q) = qmk n by rfl, sourceSLocalQuotientReflection_apply_mk,
    sourceSLocalQuotientSheetFunction_mk, sourceSLocalQuotientSheetFunction_mk,
    heq, sourceSLocalReflectionRatio_lift]

variable (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure]

theorem sourceSLocalQuotientSheetProfile_reflection (F G : U → ℂ)
    (hF : sourceSLocalSixthInvariant S F) (hG : sourceSLocalSixthInvariant S G)
    (a : U) (ρ : ℂ) (heq : ∀ x, F x = ρ * G (a * x⁻¹)) {T : ℝ} (hT : 0 < T) :
    sourceSLocalQuotientSheetProfile S hζ ν F hF T =
      ρ * sourceSLocalQuotientSheetProfile S hζ ν G hG (sLocalNorm K S a / T) := by
  let e := sourceSLocalQuotientReflection S hζ a hT
  let g := sourceSLocalQuotientSheetFunction S hζ G hG (sLocalNorm K S a / T)
  let μ := sNormOneQuotientMeasure K S ν
  have hmp : MeasurePreserving e μ μ :=
    sourceSLocalQuotientReflection_measurePreserving S hζ ν a hT
  change (∫ q, sourceSLocalQuotientSheetFunction S hζ F hF T q ∂μ) = ρ * ∫ q, g q ∂μ
  calc
    _ = ∫ q, ρ * g (e q) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall
        (sourceSLocalQuotientSheetFunction_reflection S hζ F G hF hG a ρ heq hT))
    _ = _ := by rw [integral_const_mul, hmp.integral_comp' g]

theorem sourceThetaGaussianProfile_reflection_of_pointwise (H G : ℝ → ℂ)
    (D : ℝ) (ρ : ℂ) (heq : ∀ T > 0, H T = ρ * G (D / T))
    (C₀ A₀ : ℝ) (r : ℕ) {u : ℝ} (hu : 0 < u) :
    sourceThetaGaussianProfile C₀ A₀ r 1 H u =
      ρ * sourceThetaGaussianProfile C₀ A₀ r (-1) G (D / u) := by
  rw [sourceThetaGaussianProfile_forward, sourceThetaGaussianProfile_reflected]
  unfold mellin
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  dsimp only
  rw [heq _ (mul_pos hu ht0), div_mul_eq_div_div]
  simp only [smul_eq_mul]
  ac_rfl

theorem sourceSLocalQuotientGaussian_reflection (F G : U → ℂ)
    (hF : sourceSLocalSixthInvariant S F) (hG : sourceSLocalSixthInvariant S G)
    (a : U) (ρ : ℂ) (heq : ∀ x, F x = ρ * G (a * x⁻¹))
    (C₀ A₀ : ℝ) (r : ℕ) {u : ℝ} (hu : 0 < u) :
    sourceThetaGaussianProfile C₀ A₀ r 1 (sourceSLocalQuotientSheetProfile S hζ ν F hF) u =
      ρ * sourceThetaGaussianProfile C₀ A₀ r (-1) (sourceSLocalQuotientSheetProfile S hζ ν G hG)
        (sLocalNorm K S a / u) :=
  sourceThetaGaussianProfile_reflection_of_pointwise _ _ _ _
    (fun _ hT => sourceSLocalQuotientSheetProfile_reflection S hζ ν F G hF hG a ρ heq hT) C₀ A₀ r hu

end
end ArtinMatthews.SourcePhysical
