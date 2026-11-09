module

public import ArtinMatthews.SourceSLocalQuotientSeries


set_option backward.privateInPublic true
@[expose] public section

/-! A pointwise orbit expansion gives actual sixth-invariance and
identifies the descended quotient integral with its unfolded sheets. -/
namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical ENNReal
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) {ι : Type*}
local notation "N" => SNormOne K S
local notation "Q" => SNormOneSixthQuotient K S
local notation "U" => SWholeUnits K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "qmk" => sNormOneSixthQuotientMap K S

theorem sourceSLocalSixthInvariant_of_orbit_hasSum (F : U → ℂ) (A : ι → U → ℂ)
    (h : ∀ x, HasSum (fun p : ι × Γ => A p.1 (x * (p.2.val : U))) (F x)) :
    sourceSLocalSixthInvariant S F := by
  intro x δ
  let e : ι × Γ ≃ ι × Γ := (Equiv.refl ι).prodCongr (Equiv.mulLeft δ)
  rw [← (h (x * (δ.val : U))).tsum_eq, ← (h x).tsum_eq]
  calc
    _ = ∑' p : ι × Γ, A (e p).1 (x * ((e p).2.val : U)) := by
      apply tsum_congr
      intro p
      change A p.1 ((x * (δ.val : U)) * (p.2.val : U)) =
        A p.1 (x * ((δ.val : U) * (p.2.val : U)))
      rw [mul_assoc]
    _ = _ := e.tsum_eq (fun p => A p.1 (x * (p.2.val : U)))

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "sc" => sLocalPositiveScaling K hζ S

theorem sourceSLocalQuotientSheetFunction_eq_orbitSeries (F : U → ℂ) (A : ι → U → ℂ)
    (hF : sourceSLocalSixthInvariant S F)
    (h : ∀ x, HasSum (fun p : ι × Γ => A p.1 (x * (p.2.val : U))) (F x))
    (T : ℝ) :
    sourceSLocalQuotientSheetFunction S hζ F hF T =
      sNormOnePeriodizeSeries S (fun i (n : N) => A i ((n : U) * sc T)) := by
  funext q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  let f (i : ι) (y : N) := A i ((y : U) * sc T)
  change sourceSLocalQuotientSheetFunction S hζ F hF T (qmk n) =
    sNormOnePeriodizeSeries S f (qmk n)
  have hsum : HasSum (fun p : ι × Γ => f p.1 (n * p.2.val)) (F ((n : U) * sc T)) := by
    convert h ((n : U) * sc T) using 1
    funext p
    change A p.1 (((n : U) * (p.2.val : U)) * sc T) =
      A p.1 (((n : U) * sc T) * (p.2.val : U))
    rw [mul_assoc, mul_comm (p.2.val : U) (sc T), ← mul_assoc]
  rw [sourceSLocalQuotientSheetFunction_mk, ← hsum.tsum_eq, hsum.summable.tsum_prod,
    sNormOnePeriodizeSeries]
  exact tsum_congr fun i => (sNormOnePeriodize_mk_group S (f i) n).symm

variable [Countable ι]
variable (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure]
local notation "μ" => sNormOneQuotientMeasure K S ν

theorem sourceSLocalQuotientSheetProfile_unfold_hasSum (F : U → ℂ) (A : ι → U → ℂ)
    (hF : sourceSLocalSixthInvariant S F)
    (h : ∀ x, HasSum (fun p : ι × Γ => A p.1 (x * (p.2.val : U))) (F x))
    (T : ℝ) (hm : ∀ i, Measurable (fun n : N => A i ((n : U) * sc T)))
    (hMass : (∑' i, ∫⁻ n : N, ‖A i ((n : U) * sc T)‖ₑ ∂ν) < ⊤) :
    Integrable (sourceSLocalQuotientSheetFunction S hζ F hF T) μ ∧
      sourceSLocalQuotientSheetProfile S hζ ν F hF T =
        ∑' i, sourceSLocalSheetProfile S ν hζ (A i) T := by
  have heq := sourceSLocalQuotientSheetFunction_eq_orbitSeries S hζ F A hF h T
  unfold sourceSLocalQuotientSheetProfile
  rw [heq]
  exact sNormOnePeriodizeSeries_unfold S ν (fun i n => A i ((n : U) * sc T)) hm hMass

theorem sourceSLocalQuotientSheetProfile_unfold_shifted_hasSum (F : U → ℂ)
    (A : ι → U → ℂ) (u : ι → U) (hF : sourceSLocalSixthInvariant S F)
    (h : ∀ x, HasSum (fun p : ι × Γ => A p.1 ((x * (p.2.val : U)) * u p.1)) (F x))
    {T : ℝ} (hT : 0 < T)
    (hm : ∀ i, Measurable (fun n : N => A i (((n : U) * sc T) * u i)))
    (hMass : (∑' i, ∫⁻ n : N, ‖A i (((n : U) * sc T) * u i)‖ₑ ∂ν) < ⊤) :
    Integrable (sourceSLocalQuotientSheetFunction S hζ F hF T) μ ∧
      sourceSLocalQuotientSheetProfile S hζ ν F hF T =
        ∑' i, sourceSLocalSheetProfile S ν hζ (A i) (T * sLocalNorm K S (u i)) := by
  obtain ⟨hi, heq⟩ := sourceSLocalQuotientSheetProfile_unfold_hasSum S hζ ν F
    (fun i x => A i (x * u i)) hF h T hm hMass
  refine ⟨hi, heq.trans ?_⟩
  apply tsum_congr
  intro i
  unfold sourceSLocalSheetProfile
  simp_rw [mul_assoc]
  apply sourceSLocal_sameNorm_integral S ν (A i)
  rw [sLocalNorm_mul, sLocalPositiveScaling_norm K hζ S hT,
    sLocalPositiveScaling_norm K hζ S (mul_pos hT (sLocalNorm_pos K S (u i)))]

end
end ArtinMatthews.SourcePhysical
