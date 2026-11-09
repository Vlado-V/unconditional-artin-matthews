module

public import ArtinMatthews.SourcePrincipalEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The simultaneous principal two-pole limit of the literal source
Euler continuation. The exact finite-S Dedekind residue and the factor
1/6 from the second scaling are retained. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil Set Filter
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
local notation "S" => sourceHilbertSet F S₀

def sourcePrincipalEulerExtension (q : ProbeCoordinates) : ℂ :=
  principalExteriorZeta S (6 * q.2.2) * principalExteriorZeta S q.2.1 *
    sourcePrincipalEulerAmplitude F hζ S₀ η q

def sourcePrincipalEulerDoubleRegularized (q : ProbeCoordinates) : ℂ :=
  (principalExteriorZetaRegularized S (6 * q.2.2) *
    principalExteriorZetaRegularized S q.2.1 / 6) *
      sourcePrincipalEulerAmplitude F hζ S₀ η q

theorem sourcePrincipalEulerDoubleRegularized_eq (s w z : ℂ)
    (hw : w ≠ 1) (hz : z ≠ 1 / 6) :
    sourcePrincipalEulerDoubleRegularized F hζ S₀ η (s, w, z) =
      (w - 1) * (z - 1 / 6) * sourcePrincipalEulerExtension F hζ S₀ η (s, w, z) := by
  have hz' : (6 : ℂ) * z ≠ 1 := by
    intro h
    apply hz
    linear_combination (1 / 6 : ℂ) * h
  unfold sourcePrincipalEulerDoubleRegularized sourcePrincipalEulerExtension
  dsimp only
  rw [principalExteriorZetaRegularized_eq S hz', principalExteriorZetaRegularized_eq S hw]
  ring

theorem sourcePrincipalEulerDoubleRegularized_specialize (s : ℂ) :
    sourcePrincipalEulerDoubleRegularized F hζ S₀ η (s, 1, 1 / 6) =
      (principalExteriorZetaResidue F S ^ 2 / 6) *
        (principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹) := by
  unfold sourcePrincipalEulerDoubleRegularized
  dsimp only
  rw [show (6 : ℂ) * (1 / 6) = 1 by norm_num, principalExteriorZetaRegularized_one,
    sourcePrincipalEulerAmplitude_specialize, pow_two]

theorem sourcePrincipalEulerDoubleRegularized_continuousAt
    (hM : M ≠ ⊥) (hcut : principalAngularCutoff F M ⊆ S)
    (s : ℂ) (hs : 99799 / 100000 < s.re) :
    ContinuousAt (fun wz : ℂ × ℂ => sourcePrincipalEulerDoubleRegularized F hζ S₀ η (s, wz))
      ((1 : ℂ), (1 / 6 : ℂ)) := by
  let p : ℂ × ℂ := (1, 1 / 6)
  have hp : (s, p) ∈ probeEulerOpenDomain :=
    Or.inr ⟨hs, by norm_num [p], by norm_num [p]⟩
  have hCw := (sourceGlobalCorrection_differentiableOn F hζ S₀ η hM hcut 1 one_ne_zero) (s, p) hp
  have hC := (hCw.differentiableAt (isOpen_probeEulerOpenDomain.mem_nhds hp)).continuousAt
  have hm : ContinuousAt (fun wz : ℂ × ℂ => (s, wz)) p :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hA : ContinuousAt (fun wz : ℂ × ℂ => sourcePrincipalEulerAmplitude F hζ S₀ η (s, wz)) p :=
    (hC.comp hm).mul continuousAt_const
  have hW : ContinuousAt (fun wz : ℂ × ℂ => principalExteriorZetaRegularized S wz.1) p :=
    (principalExteriorZetaRegularized_entire S).continuous.continuousAt.comp continuous_fst.continuousAt
  have hZ : ContinuousAt (fun wz : ℂ × ℂ => principalExteriorZetaRegularized S (6 * wz.2)) p :=
    (principalExteriorZetaRegularized_entire S).continuous.continuousAt.comp
      (continuousAt_const.mul continuous_snd.continuousAt)
  exact ((hZ.mul hW).div_const 6).mul hA

theorem sourcePrincipalEulerExtension_two_pole
    (hM : M ≠ ⊥) (hcut : principalAngularCutoff F M ⊆ S)
    (s : ℂ) (hs : 99799 / 100000 < s.re) :
    Tendsto (fun wz : ℂ × ℂ => (wz.1 - 1) * (wz.2 - 1 / 6) *
      sourcePrincipalEulerExtension F hζ S₀ η (s, wz))
      ((𝓝[≠] (1 : ℂ)) ×ˢ (𝓝[≠] (1 / 6 : ℂ)))
      (𝓝 ((principalExteriorZetaResidue F S ^ 2 / 6) *
        (principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹))) := by
  let f : Filter (ℂ × ℂ) := (𝓝[≠] (1 : ℂ)) ×ˢ (𝓝[≠] (1 / 6 : ℂ))
  have hf : f ≤ 𝓝 ((1 : ℂ), (1 / 6 : ℂ)) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  have H := (sourcePrincipalEulerDoubleRegularized_continuousAt F hζ S₀ η hM hcut s hs).tendsto.mono_left hf
  change Tendsto _ f (𝓝 (sourcePrincipalEulerDoubleRegularized F hζ S₀ η (s, 1, 1 / 6))) at H
  rw [sourcePrincipalEulerDoubleRegularized_specialize] at H
  apply H.congr'
  have hw : ∀ᶠ wz : ℂ × ℂ in f, wz.1 ≠ 1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hz : ∀ᶠ wz : ℂ × ℂ in f, wz.2 ≠ 1 / 6 :=
    tendsto_snd.eventually self_mem_nhdsWithin
  filter_upwards [hw, hz] with wz hwz hzz
  exact sourcePrincipalEulerDoubleRegularized_eq F hζ S₀ η s wz.1 wz.2 hwz hzz

variable [IsTotallyComplex F]

theorem sourcePrincipalEulerExtension_initial
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hcut : probePrimeCutoff F ⊆ S) (s w z : ℂ) (hs : 2 < s.re)
    (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    sourceGlobalCalF F hζ S₀ hS η 1 s w z = sourcePrincipalEulerExtension F hζ S₀ η (s, w, z) :=
  sourceGlobalCalF_principal F hζ S₀ η hS hcut s w z hs hw hz

end
end ArtinMatthews.SourceEulerAssembly
