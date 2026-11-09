module

public import ArtinMatthews.SourceContinuedPoissonRowIntegral
public import ArtinMatthews.SourceContinuedPoissonRowSlices


set_option backward.privateInPublic true
@[expose] public section

/-! Integrate the coordinate shifts using absolute Fubini in the actual
height measure. This gives both fixed nonprincipal moves of source06. -/
namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

theorem sourcePoissonHeight_integral_xi_inside (f : SourcePoissonHeights → ℂ)
    (hf : Integrable f sourcePoissonHeightMeasure) :
    (∫ p, f p ∂sourcePoissonHeightMeasure) = ∫ wt : ℝ × ℝ, ∫ x : ℝ, f (wt,x) :=
  integral_prod f hf

theorem sourcePoissonHeight_integral_z_inside (f : SourcePoissonHeights → ℂ)
    (hf : Integrable f sourcePoissonHeightMeasure) :
    (∫ p, f p ∂sourcePoissonHeightMeasure) = ∫ x : ℝ, ∫ y : ℝ, ∫ t : ℝ, f ((y,t),x) := by
  rw [show (∫ p, f p ∂sourcePoissonHeightMeasure) = ∫ x : ℝ, ∫ wt : ℝ × ℝ, f (wt,x)
      from integral_prod_symm f hf]
  apply integral_congr_ae
  have h : ∀ᵐ x : ℝ, Integrable (fun wt : ℝ × ℝ => f (wt,x)) ((volume : Measure ℝ).prod volume) :=
    Integrable.prod_left_ae hf
  filter_upwards [h] with x hx using integral_prod _ hx

theorem sourcePoissonHeight_integral_w_inside (f : SourcePoissonHeights → ℂ)
    (hf : Integrable f sourcePoissonHeightMeasure) :
    (∫ p, f p ∂sourcePoissonHeightMeasure) = ∫ x : ℝ, ∫ t : ℝ, ∫ y : ℝ, f ((y,t),x) := by
  rw [show (∫ p, f p ∂sourcePoissonHeightMeasure) = ∫ x : ℝ, ∫ wt : ℝ × ℝ, f (wt,x)
      from integral_prod_symm f hf]
  apply integral_congr_ae
  have h : ∀ᵐ x : ℝ, Integrable (fun wt : ℝ × ℝ => f (wt,x)) ((volume : Measure ℝ).prod volume) :=
    Integrable.prod_left_ae hf
  filter_upwards [h] with x hx using integral_prod_symm _ hx

end
end ArtinMatthews.SourcePhysical

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Set MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "I" => sourceContinuedPoissonRowIntegral F S₀ hζ η hJ
local notation "L" => sourceContinuedPoissonRowOnLines F S₀ hζ η hJ

theorem sourceContinuedPoissonRowIntegral_initial
    (hS : standardWeilBadPlaces F ⊆ S) (hcut : probePrimeCutoff F ⊆ S)
    (v : InfinitePlace F) (u : {a : R // a ≠ 0}) (X Y Z : ℝ) :
    I v u X Y Z 4 4 2 = (1/(2*Real.pi) : ℂ)^3 *
      ∫ p, sourcePoissonTripleKernel X Y Z 4 4 2
        (fun t => sourceProbeW1Mellin (sourcePoissonVertical 4 t))
        (fun t => sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical 2 t))
        (sourcePoissonInitialRows F S₀ hζ hS η {u}) p ∂sourcePoissonHeightMeasure := by
  unfold sourceContinuedPoissonRowIntegral
  apply congrArg ((1/(2*Real.pi) : ℂ)^3 * ·)
  exact integral_congr_ae (ae_of_all _ (sourceContinuedPoissonRowKernel_initial F S₀ hζ η hJ hS hcut v u X Y Z))

theorem sourceContinuedPoissonRowIntegral_shift_xi
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (w z : ℝ) (hw : 3/1000 ≤ w) (hz : 2/5 ≤ z) :
    I v u X Y Z a w z = I v u X Y Z b w z := by
  have h (x : ℝ) (hx : 1 < x) :=
    sourceContinuedPoissonRowOnLines_integrable_right F S₀ hζ η hJ v u hcut hu hX hY hZ x w z hx hw hz
  unfold sourceContinuedPoissonRowIntegral
  apply congrArg ((1/(2*Real.pi) : ℂ)^3 * ·)
  rw [sourcePoissonHeight_integral_xi_inside _ (h a ha),
    sourcePoissonHeight_integral_xi_inside _ (h b (ha.trans_le hab))]
  apply integral_congr_ae
  filter_upwards with wt
  exact sourceContinuedPoissonRowKernel_shift_xi F S₀ hζ η hJ hcut v u hu hX hY hZ ha hab
    (sourcePoissonVertical w wt.1) (sourcePoissonVertical z wt.2)
    (by simpa only [sourcePoissonVertical_re] using hw) (by simpa only [sourcePoissonVertical_re] using hz)

theorem sourceContinuedPoissonRowIntegral_shift_z
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    {a b : ℝ} (ha : 2/5 ≤ a) (hab : a ≤ b) (ξ w : ℝ) (hξ : 1 < ξ) (hw : 3/1000 ≤ w) :
    I v u X Y Z ξ w a = I v u X Y Z ξ w b := by
  have h (x : ℝ) (hx : 2/5 ≤ x) :=
    sourceContinuedPoissonRowOnLines_integrable_right F S₀ hζ η hJ v u hcut hu hX hY hZ ξ w x hξ hw hx
  unfold sourceContinuedPoissonRowIntegral
  apply congrArg ((1/(2*Real.pi) : ℂ)^3 * ·)
  rw [sourcePoissonHeight_integral_z_inside _ (h a ha),
    sourcePoissonHeight_integral_z_inside _ (h b (ha.trans hab))]
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with y
  exact sourceContinuedPoissonRowKernel_shift_z F S₀ hζ η hJ hcut v u hu hX hY hZ ha hab
    (sourcePoissonVertical ξ x) (sourcePoissonVertical w y)
    (by simpa only [sourcePoissonVertical_re] using hξ) (by simpa only [sourcePoissonVertical_re] using hw)

theorem sourceContinuedPoissonRowIntegral_shift_w
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    {a b : ℝ} (ha : 3/1000 ≤ a) (hab : a ≤ b) (ξ z : ℝ) (hξ : 1 < ξ) (hz : 2/5 ≤ z) :
    I v u X Y Z ξ a z = I v u X Y Z ξ b z := by
  have h (x : ℝ) (hx : 3/1000 ≤ x) :=
    sourceContinuedPoissonRowOnLines_integrable_right F S₀ hζ η hJ v u hcut hu hX hY hZ ξ x z hξ hx hz
  unfold sourceContinuedPoissonRowIntegral
  apply congrArg ((1/(2*Real.pi) : ℂ)^3 * ·)
  rw [sourcePoissonHeight_integral_w_inside _ (h a ha),
    sourcePoissonHeight_integral_w_inside _ (h b (ha.trans hab))]
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with t
  exact sourceContinuedPoissonRowKernel_shift_w F S₀ hζ η hJ hcut v u hu hX hY hZ ha hab
    (sourcePoissonVertical ξ x) (sourcePoissonVertical z t)
    (by simpa only [sourcePoissonVertical_re] using hξ) (by simpa only [sourcePoissonVertical_re] using hz)

theorem sourceContinuedPoissonRowIntegral_low_w
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    I v u X Y Z 4 4 2 = I v u X Y Z principalProbeSigma (3/1000) (2/5) := by
  have hs : 1 < principalProbeSigma := by norm_num [principalProbeSigma]
  calc
    _ = I v u X Y Z principalProbeSigma 4 2 :=
      (sourceContinuedPoissonRowIntegral_shift_xi F S₀ hζ η hJ hcut v u hu hX hY hZ
        hs (by norm_num [principalProbeSigma]) 4 2 (by norm_num) (by norm_num)).symm
    _ = I v u X Y Z principalProbeSigma 4 (2/5) :=
      (sourceContinuedPoissonRowIntegral_shift_z F S₀ hζ η hJ hcut v u hu hX hY hZ
        le_rfl (by norm_num) principalProbeSigma 4 hs (by norm_num)).symm
    _ = _ := (sourceContinuedPoissonRowIntegral_shift_w F S₀ hζ η hJ hcut v u hu hX hY hZ
      le_rfl (by norm_num) principalProbeSigma (2/5) hs le_rfl).symm

theorem sourceContinuedPoissonRowIntegral_far_z
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    I v u X Y Z 4 4 2 = I v u X Y Z 4 4 350000 :=
  sourceContinuedPoissonRowIntegral_shift_z F S₀ hζ η hJ hcut v u hu hX hY hZ
    (by norm_num) (by norm_num) 4 4 (by norm_num) (by norm_num)

end
end ArtinMatthews.SourceEulerAssembly
