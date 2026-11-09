module

public import ArtinMatthews.SourceKPTameParametricOpenCell
public import ArtinMatthews.SourceKPTameIntertwiningAbsolute
public import ArtinMatthews.SourceKPExceptionalLocalFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The actual spherical intertwining integral in the genuine tame
principal series, with the exceptional normalization retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical StandardAdelic
open AllowedGenerators VaryingKummerAnalytic
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "fₛ[" s "]" => Subtype.val (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s)
local notation "μ₀" => sourceJacquetHaar K P.val

def sourceKPTameSphericalIntertwiner (s : ℂ) : ZMod 3 → ℂ :=
  ∫ x : L, fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) ∂μ₀

theorem sourceKPTameSphericalIntertwiner_integrable (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun x : L => fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))) μ₀ := by
  have he : (fun x : L => fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))) =
      sourceKPTameIntertwiningIntegrand K hζ S₀ P s :=
    funext (sourceKPTameParametricSpherical_open K hζ S₀ P s)
  rw [he]
  exact sourceKPTameIntertwiningIntegrand_integrable K hζ S₀ P hP hs

theorem sourceKPTameSphericalIntertwiner_eq (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) :
    sourceKPTameSphericalIntertwiner K hζ S₀ P s =
      sourceKPUnramifiedScatteringFactor P.val s • sourceJacquetBasis 0 := by
  unfold sourceKPTameSphericalIntertwiner
  simp_rw [sourceKPTameParametricSpherical_open K hζ S₀ P s]
  exact sourceKPTameIntertwiningIntegral_eq K hζ S₀ P hP hs

theorem sourceKPTameSphericalIntertwiner_exceptional (hP : P.val ∉ traceBadPlaces K) :
    sourceKPTameSphericalIntertwiner K hζ S₀ P (1/6) =
      (1+(Ideal.absNorm P.val.asIdeal : ℂ)⁻¹) • sourceJacquetBasis 0 := by
  rw [sourceKPTameSphericalIntertwiner_eq K hζ S₀ P hP (by norm_num),
    sourceKPUnramifiedScatteringFactor_exceptional]

theorem sourceKPTameSphericalIntertwiner_exceptional_ne_zero (hP : P.val ∉ traceBadPlaces K) :
    sourceKPTameSphericalIntertwiner K hζ S₀ P (1/6) ≠ 0 := by
  rw [sourceKPTameSphericalIntertwiner_eq K hζ S₀ P hP (by norm_num)]
  apply smul_ne_zero (sourceKPUnramifiedScatteringFactor_exceptional_ne_zero P.val)
  intro h
  have hv := congrArg (fun v : ZMod 3 → ℂ => v 0) h
  simp [sourceJacquetBasis] at hv

end
end ArtinMatthews
