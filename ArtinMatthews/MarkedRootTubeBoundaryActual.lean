module

public import ArtinMatthews.MarkedRootTubeBoundary
public import ArtinMatthews.MarkedRootBoundaryScalar


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine original root-parameter boundary is small before and
after integration. The factor fifteen is the exact normalized measure
mass, retained explicitly for the final physical moment estimate. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (hinj : Function.Injective e)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ u,‖η u‖≤1)
  (q ρ G H A W : ℝ) (hq₀ : 0≤q) (hq₁ : q≤1)
  (hρ : 0<ρ) (hρ₁ : ρ<1) (hgap : Real.sqrt q<ρ^2)
  (hG : 0<G) (hH : 1≤H) (hA : 0≤A) (hW : 0≤W)
  (hdepth : 100*(5*G+36)<(Fintype.card J:ℝ))
  (hψ : ∀ u,‖ψ u‖≤W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A)

include he hinj hη hηnorm hq₀ hq₁ hρ hρ₁ hgap hG hH hA hW hdepth hψ hsupp

theorem markedRootTubeBoundary_actual_bound :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0<d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ))≤Y →
      Y≤Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      ∀ (R : ℕ) (hR : 1≤R) (U V : ℝ) (p : ℝ × (ℝ × ℝ))
        (_hp : p∈markedRootBoxDomain) (orientation : ℕ → Bool),
      ‖markedRootTubeBoundary e x ψ η d₀ Y ((Real.log x)^(G+9)) q ρ
        R hR U V p orientation‖≤((Real.log x)^(-G))^(markedMemoryMomentLength x) := by
  filter_upwards [markedRootWindowGoodBoundary_actual_bound e he hinj ψ η hη hηnorm
    q ρ G H A W hq₀ hq₁ hρ hρ₁ hgap hG hH hA hW hdepth hψ hsupp] with x hx
  intro d₀ Y hd₀ hYlo hYhi R hR U V p hp orientation
  rw [markedRootTubeBoundary_eq_window e x ψ η d₀ Y ((Real.log x)^(G+9)) q ρ R hR U V p hp orientation]
  exact hx d₀ Y hd₀ hYlo hYhi R hR U V p hp orientation

theorem markedRootTubeBoundary_integral_actual_bound :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0<d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ))≤Y →
      Y≤Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      ∀ (R : ℕ) (hR : 1≤R) (U V : ℝ) (orientation : ℕ → Bool),
      ‖∫ p,markedRootTubeBoundary e x ψ η d₀ Y ((Real.log x)^(G+9)) q ρ
        R hR U V p orientation ∂markedNormalizedRootMeasure‖≤
        15*((Real.log x)^(-G))^(markedMemoryMomentLength x) := by
  filter_upwards [markedRootTubeBoundary_actual_bound e he hinj ψ η hη hηnorm
    q ρ G H A W hq₀ hq₁ hρ hρ₁ hgap hG hH hA hW hdepth hψ hsupp] with x hx
  intro d₀ Y hd₀ hYlo hYhi R hR U V orientation
  exact markedNormalizedRoot_integral_norm_le _ _
    (fun p hp => hx d₀ Y hd₀ hYlo hYhi R hR U V p hp orientation)

end ArtinMatthews
