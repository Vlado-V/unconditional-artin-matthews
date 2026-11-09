module

public import ArtinMatthews.SourceKPAdelicHaarDilation
public import ArtinMatthews.SourceKPAdelicOutgoingWeylModular


set_option backward.privateInPublic true
@[expose] public section

/-! The torus covariance of the measured standard operator uses the
literal Weyl conjugation, full idele Haar modulus, and exact J transport. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "A" => 𝔸[K]
local notation "I" => IdeleGroup (𝓞 K) K
local notation "G" => SourceKPAdelicProjective K hζ
local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "F" => sourceKPAdelicCompactSection K hζ
local notation "W" => sourceKPAdelicProjectiveWeyl K hζ
local notation "w" => sourceKPAdelicCoveringTorusWeyl K hζ
local notation "N" => sourceKPAdelicUpperLift K hζ
local notation "a₀" => sourceKPAdelicTorusIdele K hζ
local notation "d₀" => sourceKPAdelicBorelTorusInclusion K hζ
local notation "δ" => sourceKPAdelicBorelModularHalf K hζ
local notation "D" => sourceKPIdeleAbsoluteNorm K
local notation "J" => sourceKPAdelicTorusWeylTransport K hζ
local notation "ρ" => sourceKPAdelicNormalizedBorelRepresentation K hζ
local notation "τ" => sourceKPAdelicTorusInducedRepresentation K hζ
local notation "μ₀" => sourceKPAdelicTraceProduct K
local notation "C" => sourceKPAdelicCoordinateKernel K hζ
local notation "M" => sourceKPAdelicCoordinateIntegral K hζ μ₀

local instance sourceKPAdelicOutgoingTorusMeasurable : MeasurableSpace A := borel A
local instance sourceKPAdelicOutgoingTorusBorel : BorelSpace A := ⟨rfl⟩

theorem sourceKPAdelicOutgoingKernel_torus (s : ℂ) (t : T) (g : G) (u : T) (x : A) :
    C s (t.val*g) u x =
      δ (d₀ (w t))*C s g (u*w t) ((((a₀ t)⁻¹ : I) : A)*x) := by
  let x' : A := (((a₀ t)⁻¹ : I) : A)*x
  have hx : (a₀ t : A)*x' = x := by
    change (a₀ t : A)*((((a₀ t)⁻¹ : I) : A)*x) = x
    rw [← mul_assoc,← Units.val_mul,mul_inv_cancel,Units.val_one,one_mul]
  have ht := sourceKPAdelicTorus_upper K hζ t x'
  rw [hx] at ht
  have hw := (sourceKPAdelicTorus_left_weyl K hζ (w t)).symm
  rw [sourceKPAdelicCoveringTorusWeyl_involutive K hζ t] at hw
  have hg : W*N x*(t.val*g) = (w t).val*(W*N x'*g) := by
    calc
      _ = W*(N x*t.val)*g := by group
      _ = (W*t.val)*N x'*g := by rw [← ht]; group
      _ = _ := by rw [hw]; group
  have h := congrArg (fun v : V s => v.val u)
    ((F s).property (d₀ (w t)) (W*N x'*g))
  change ((F s).val ((w t).val*(W*N x'*g))).val u =
    δ (d₀ (w t))*((F s).val (W*N x'*g)).val
      (u*sourceKPAdelicBorelTorusProjection K hζ (d₀ (w t))) at h
  rw [sourceKPAdelicBorelTorusProjection_inclusion] at h
  unfold sourceKPAdelicCoordinateKernel
  rw [hg]
  exact h

theorem sourceKPAdelicOutgoingCoordinateIntegral_torus (s : ℂ) (t : T) (g : G) :
    M s (t.val*g) = (D (a₀ t) : ℂ) • ρ s (d₀ (w t)) (M s g) := by
  apply Subtype.ext
  funext u
  change (∫ x, C s (t.val*g) u x ∂μ₀) =
    (D (a₀ t) : ℂ)*(δ (d₀ (w t))*∫ x, C s g
      (u*sourceKPAdelicBorelTorusProjection K hζ (d₀ (w t))) x ∂μ₀)
  rw [sourceKPAdelicBorelTorusProjection_inclusion]
  simp_rw [sourceKPAdelicOutgoingKernel_torus K hζ s t g]
  rw [integral_const_mul,sourceKPAdelicTraceHaar_integral_inv_mul K hζ (a₀ t)
    (fun x => C s g (u*w t) x),mul_left_comm]

theorem sourceKPAdelicOutgoingWeyl_transport (s : ℂ) (t : T) (v : V s) :
    J s ((D (a₀ t) : ℂ) • ρ s (d₀ (w t)) v) = ρ (-s) (d₀ t) (J s v) := by
  have hρ (p : ℂ) (a : T) (u : V p) : ρ p (d₀ a) u = δ (d₀ a) • τ p a u := by
    change δ (d₀ a) • τ p (sourceKPAdelicBorelTorusProjection K hζ (d₀ a)) u = _
    rw [sourceKPAdelicBorelTorusProjection_inclusion]
  rw [hρ,hρ,map_smul,map_smul,sourceKPAdelicTorusWeylTransport_right_conjugate,
    smul_smul,sourceKPAdelicOutgoingWeyl_half K hζ t]

theorem sourceKPAdelicOutgoingValue_torus (s : ℂ) (t : T) (g : G) :
    sourceKPAdelicSphericalIntertwinerValue K hζ μ₀ s (t.val*g) =
      ρ (-s) (d₀ t) (sourceKPAdelicSphericalIntertwinerValue K hζ μ₀ s g) := by
  change J s (M s (t.val*g)) = ρ (-s) (d₀ t) (J s (M s g))
  rw [sourceKPAdelicOutgoingCoordinateIntegral_torus K hζ s t g,
    sourceKPAdelicOutgoingWeyl_transport K hζ s t]

end
end ArtinMatthews
