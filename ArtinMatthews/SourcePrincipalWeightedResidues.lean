module

public import ArtinMatthews.SourcePrincipalContourKernel
public import ArtinMatthews.PrincipalAngularMellinSignal


set_option backward.privateInPublic true
@[expose] public section

/-! The physical weight preserves the two genuine principal Dedekind residues.
The (z)-regularizer retains its factor of (1/6). -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Set Filter
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open OAI.SevenEighths.Continuation
open scoped NumberField Classical Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀
local notation "RS" => principalExteriorZetaResidue F S

def sourcePrincipalPoissonWRegularized (X Y Z : ℝ) (q : ProbeCoordinates) : ℂ :=
  sourcePrincipalPoissonWeight F hζ S₀ v X Y Z q *
    (principalExteriorZeta S (6 * q.2.2) * principalExteriorZetaRegularized S q.2.1 *
      sourcePrincipalEulerAmplitude F hζ S₀ η q)

def sourcePrincipalPoissonWResidue (X Y Z : ℝ) (ξ z : ℂ) : ℂ :=
  sourcePrincipalPoissonWeight F hζ S₀ v X Y Z (ξ, 1, z) *
    (principalExteriorZeta S (6 * z) * RS * sourcePrincipalEulerAmplitude F hζ S₀ η (ξ, 1, z))

def sourcePrincipalPoissonZRegularized (X Y Z : ℝ) (ξ z : ℂ) : ℂ :=
  sourcePrincipalPoissonWeight F hζ S₀ v X Y Z (ξ, 1, z) *
    ((principalExteriorZetaRegularized S (6 * z) / 6) * RS *
      sourcePrincipalEulerAmplitude F hζ S₀ η (ξ, 1, z))

theorem sourcePrincipalPoissonWRegularized_eq (X Y Z : ℝ) (ξ w z : ℂ) (hw : w ≠ 1) :
    sourcePrincipalPoissonWRegularized F hζ S₀ η v X Y Z (ξ, w, z) =
      (w - 1) * sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z (ξ, w, z) := by
  unfold sourcePrincipalPoissonWRegularized sourcePrincipalPoissonKernel sourcePrincipalEulerExtension
  dsimp only
  rw [principalExteriorZetaRegularized_eq S hw]
  ring

theorem sourcePrincipalPoissonWRegularized_one (X Y Z : ℝ) (ξ z : ℂ) :
    sourcePrincipalPoissonWRegularized F hζ S₀ η v X Y Z (ξ, 1, z) =
      sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z ξ z := by
  unfold sourcePrincipalPoissonWRegularized sourcePrincipalPoissonWResidue
  dsimp only
  rw [principalExteriorZetaRegularized_one]

theorem sourcePrincipalPoissonZRegularized_eq (X Y Z : ℝ) (ξ z : ℂ) (hz : z ≠ 1 / 6) :
    sourcePrincipalPoissonZRegularized F hζ S₀ η v X Y Z ξ z =
      (z - 1 / 6) * sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z ξ z := by
  have hz' : (6 : ℂ) * z ≠ 1 := by
    intro he
    apply hz
    linear_combination (1 / 6 : ℂ) * he
  unfold sourcePrincipalPoissonZRegularized sourcePrincipalPoissonWResidue
  rw [principalExteriorZetaRegularized_eq S hz']
  ring

theorem sourcePrincipalPoissonZRegularized_eq_double (X Y Z : ℝ) (ξ z : ℂ) :
    sourcePrincipalPoissonZRegularized F hζ S₀ η v X Y Z ξ z =
      sourcePrincipalPoissonWeight F hζ S₀ v X Y Z (ξ, 1, z) *
        sourcePrincipalEulerDoubleRegularized F hζ S₀ η (ξ, 1, z) := by
  unfold sourcePrincipalPoissonZRegularized sourcePrincipalEulerDoubleRegularized
  dsimp only
  rw [principalExteriorZetaRegularized_one]
  ring

/-- The literal residue constant retains the two finite-S zeta residues and both weights. -/
def sourcePrincipalPoissonDoubleConstant : ℂ :=
  RS ^ 2 / 6 * sourceSLocalProbeMellin F hζ S v (1 / 6) * sourceProbeW1Mellin 1

theorem sourcePrincipalPoissonDoubleConstant_eq :
    sourcePrincipalPoissonDoubleConstant F hζ S₀ v =
      RS ^ 2 / 6 * sourceSLocalProbeMellin F hζ S v (1 / 6) := by
  rw [sourcePrincipalPoissonDoubleConstant, sourceProbeW1Mellin_one, mul_one]

theorem sourcePrincipalPoissonDoubleConstant_ne_zero :
    sourcePrincipalPoissonDoubleConstant F hζ S₀ v ≠ 0 := by
  rw [sourcePrincipalPoissonDoubleConstant_eq]
  exact mul_ne_zero
    (div_ne_zero (pow_ne_zero _ (principalExteriorZetaResidue_ne_zero S)) (by norm_num))
    (sourceSLocalProbeMellin_sixth_ne_zero F hζ S v)

def sourcePrincipalPoissonDoubleKernel (Z : ℝ) (ξ : ℂ) : ℂ :=
  gaussianContourIntegrand
    (fun s => principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹)
    (-8 / 15) Z ξ

theorem sourcePrincipalPoissonWeight_specialize {Z : ℝ} (hZ : 0 < Z) (ξ : ℂ) :
    sourcePrincipalPoissonWeight F hζ S₀ v (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z
      (ξ, 1, 1 / 6) =
      (Z : ℂ) ^ (ξ - 8 / 15) * Complex.exp ((ξ - 5 / 6) ^ 2) *
        sourceSLocalProbeMellin F hζ S v (1 / 6) := by
  unfold sourcePrincipalPoissonWeight
  dsimp only
  rw [sourceProbeW1Mellin_one]
  simp only [sub_self, Complex.cpow_zero, mul_one]
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le (9 / 10 : ℝ) (1 / 2 - 1 / 6 : ℂ),
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hZ.ne')]
  have he : ((9 / 10 : ℝ) : ℂ) * (1 / 2 - 1 / 6) + (ξ + 1 / 6 - 1) = ξ - 8 / 15 := by
    push_cast
    ring
  rw [he, show ξ + 1 / 6 - 1 = ξ - 5 / 6 by ring]

/-- At the sequential second pole the original scales yield the actual Gaussian angular kernel. -/
theorem sourcePrincipalPoissonZRegularized_sixth {Z : ℝ} (hZ : 0 < Z) (ξ : ℂ) :
    sourcePrincipalPoissonZRegularized F hζ S₀ η v (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z
      ξ (1 / 6) =
      sourcePrincipalPoissonDoubleConstant F hζ S₀ v * sourcePrincipalPoissonDoubleKernel F hζ S₀ η Z ξ := by
  rw [sourcePrincipalPoissonZRegularized_eq_double, sourcePrincipalEulerDoubleRegularized_specialize,
    sourcePrincipalPoissonWeight_specialize F hζ S₀ v hZ, sourcePrincipalPoissonDoubleConstant_eq]
  unfold sourcePrincipalPoissonDoubleKernel gaussianContourIntegrand
  have he : ξ + ((-8 / 15 : ℝ) : ℂ) = ξ - 8 / 15 := by push_cast; ring
  rw [he]
  ring

theorem sourcePrincipalPoissonKernel_two_pole
    (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ S)
    {Z : ℝ} (hZ : 0 < Z) (ξ : ℂ) (hξ : 99799 / 100000 < ξ.re) :
    Tendsto (fun wz : ℂ × ℂ => (wz.1 - 1) * (wz.2 - 1 / 6) *
      sourcePrincipalPoissonKernel F hζ S₀ η v (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z (ξ, wz))
      ((𝓝[≠] (1 : ℂ)) ×ˢ (𝓝[≠] (1 / 6 : ℂ)))
      (𝓝 (sourcePrincipalPoissonDoubleConstant F hζ S₀ v *
        sourcePrincipalPoissonDoubleKernel F hζ S₀ η Z ξ)) := by
  let p : ℂ × ℂ := (1, 1 / 6)
  let D : Set (ℂ × ℂ) := {wz | 0 < wz.2.re}
  let f : Filter (ℂ × ℂ) := (𝓝[≠] (1 : ℂ)) ×ˢ (𝓝[≠] (1 / 6 : ℂ))
  let X := Z ^ (9 / 10 : ℝ)
  let Y := Z ^ (133 / 1000 : ℝ)
  let W (wz : ℂ × ℂ) := sourcePrincipalPoissonWeight F hζ S₀ v X Y Z (ξ, wz)
  have hp : p ∈ D := by norm_num [p, D, Complex.div_re]
  have hD : IsOpen D := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)
  have hf : f ≤ 𝓝 p := by
    change f ≤ 𝓝 ((1 : ℂ), (1 / 6 : ℂ))
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  have hW : DifferentiableOn ℂ W D :=
    sourcePrincipalPoissonWeight_differentiableOn_path F hζ S₀ v
      (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
      (fun wz : ℂ × ℂ => (ξ, wz)) ((differentiableOn_const ξ).prodMk differentiableOn_id)
      (fun _ hwz => hwz)
  have h := ((hW.differentiableAt (hD.mem_nhds hp)).continuousAt.tendsto.mono_left hf).mul
    (sourcePrincipalEulerExtension_two_pole F hζ S₀ η hJ hcut ξ hξ)
  have he :
      W p * ((RS ^ 2 / 6) *
        (principalAngularCorrection hζ η S ξ * (principalAngularExteriorL η S ξ)⁻¹)) =
      sourcePrincipalPoissonDoubleConstant F hζ S₀ v * sourcePrincipalPoissonDoubleKernel F hζ S₀ η Z ξ := by
    rw [← sourcePrincipalPoissonZRegularized_sixth F hζ S₀ η v hZ,
      sourcePrincipalPoissonZRegularized_eq_double, sourcePrincipalEulerDoubleRegularized_specialize]
  rw [he] at h
  apply h.congr'
  filter_upwards with wz
  unfold sourcePrincipalPoissonKernel W
  ring

end
end ArtinMatthews.SourceEulerAssembly
