module

public import ArtinMatthews.SourceKPAdelicCoordinateParameter
public import Mathlib.MeasureTheory.Group.Integral


set_option backward.privateInPublic true
@[expose] public section

/-! The measured outgoing value is left upper invariant and right
fixed by the exact original deep compact level. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "A" => 𝔸[K]
local notation "G" => SourceKPAdelicProjective K hζ
local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ
local notation "F" => sourceKPAdelicCompactSection K hζ
local notation "W" => sourceKPAdelicProjectiveWeyl K hζ
local notation "N" => sourceKPAdelicUpperLift K hζ
local notation "M" => sourceKPAdelicSphericalIntertwinerValue K hζ (sourceKPAdelicTraceProduct K)
local notation "C" => sourceKPAdelicCoordinateKernel K hζ

local instance sourceKPAdelicOutgoingTranslationMeasurable : MeasurableSpace A := borel A
local instance sourceKPAdelicOutgoingTranslationBorel : BorelSpace A := ⟨rfl⟩

theorem sourceKPAdelicOutgoingKernel_upper (s : ℂ) (u : A) (g : G) (t : T) (x : A) :
    C s (N u*g) t x = C s g t (x+u) := by
  have h : W*N x*(N u*g) = W*N (x+u)*g := by
    rw [sourceKPAdelicUpperLift_add K hζ x u]
    group
  unfold sourceKPAdelicCoordinateKernel
  rw [h]

theorem sourceKPAdelicOutgoingValue_upper (s : ℂ) (u : A) (g : G) :
    M s (N u*g) = M s g := by
  apply Subtype.ext
  funext t
  simp only [sourceKPAdelicSphericalIntertwinerValue_apply]
  simp_rw [sourceKPAdelicOutgoingKernel_upper K hζ s u g]
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  exact integral_add_right_eq_self _ u

theorem sourceKPAdelicOutgoingKernel_deep_right (s : ℂ) (g : G) (k : D) (t : T) (x : A) :
    C s (g*k.val) t x = C s g t x := by
  have h := congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s =>
    (f.val (W*N x*g)).val t) (sourceKPAdelicCompactSection_right K hζ s k)
  change ((F s).val ((W*N x*g)*k.val)).val t = ((F s).val (W*N x*g)).val t at h
  unfold sourceKPAdelicCoordinateKernel
  rw [← mul_assoc]
  exact h

theorem sourceKPAdelicOutgoingValue_deep_right (s : ℂ) (g : G) (k : D) :
    M s (g*k.val) = M s g := by
  apply Subtype.ext
  funext t
  simp only [sourceKPAdelicSphericalIntertwinerValue_apply]
  simp_rw [sourceKPAdelicOutgoingKernel_deep_right K hζ s g k]

end
end ArtinMatthews
