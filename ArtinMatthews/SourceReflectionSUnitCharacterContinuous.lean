module

public import ArtinMatthews.SourceReflectionSUnitCharacter
public import ArtinMatthews.SourceKPRetainedTinySixth
public import Mathlib.Topology.Algebra.Group.Neighborhood


set_option backward.privateInPublic true
@[expose] public section

/-! The actual row phase is locally constant at one and continuous on the whole S-local group. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Filter SourcePhysical
open scoped NumberField Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "X" => exteriorUnitSubgroup S

theorem sourceReflectionSUnitCharacter_continuous (u : X) :
    Continuous (sourceReflectionSUnitCharacter K hζ S₀ u) := by
  let χ := sourceReflectionSUnitCharacter K hζ S₀ u
  choose M hM hroot using fun v : S => sourceKPRetained_tiny_sixth K v.val
  have hn (v : S) : ∀ᶠ x : U in 𝓝 1,
      ((x.2 v : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)-1 ∈
        sourceLocalBall K v.val (-(M v : ℤ)) := by
    let f (x : U) : v.1.adicCompletion K := (x.2 v : v.1.adicCompletion K)-1
    have hc : Continuous f := (Units.continuous_val.comp
      ((continuous_apply v).comp continuous_snd)).sub continuous_const
    have hf : f 1 = 0 := sub_self 1
    have hzero : f 1 ∈ sourceLocalBall K v.val (-(M v : ℤ)) := by
      rw [hf]
      exact (sourceLocalOpenBall K v.val (-(M v : ℤ))).zero_mem
    exact hc.continuousAt ((sourceLocalBall_isOpen K v.val _).mem_nhds hzero)
  apply continuous_of_tendsto_nhds_one χ
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_all.mpr hn] with x hx
  choose z hz using fun v => hroot v (x.2 v) (hx v)
  have he : x.2 = (1 : U).2 * z^6 := by
    funext v
    change x.2 v = 1 * z v ^ 6
    rw [one_mul, hz v]
  exact ((sourceReflectionSUnitCharacter_eq_of_finite_sixth_mul K hζ S₀ u z he).trans
    (map_one χ)).symm

theorem sourceReflectionSUnitCharacter_val_measurable [MeasurableSpace U] [BorelSpace U]
    (u : X) : Measurable (fun x : U => (sourceReflectionSUnitCharacter K hζ S₀ u x : ℂ)) :=
  (Units.continuous_val.comp (sourceReflectionSUnitCharacter_continuous K hζ S₀ u)).measurable

theorem sourceReflectionSUnitCharacter_measurable [MeasurableSpace U] [BorelSpace U]
    (u : X) : Measurable (sourceReflectionSUnitCharacter K hζ S₀ u) :=
  measurable_comap_iff.mpr (sourceReflectionSUnitCharacter_val_measurable K hζ S₀ u)

end
end ArtinMatthews.SourceEulerAssembly
