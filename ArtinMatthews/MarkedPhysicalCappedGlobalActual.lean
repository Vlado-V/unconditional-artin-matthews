module

public import ArtinMatthews.MarkedPhysicalCappedGlobalFlatten
public import ArtinMatthews.MarkedPhysicalCappedVolumeActual
public import ArtinMatthews.MarkedArrayBandStructure


set_option backward.privateInPublic true
@[expose] public section

/-! The literal actual capped global term has the original logarithmic
moment saving. Its exact independent-line baseline remains in the
identification and is contracted only by its proved actual bounds. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedPhysicalCoordinateCappedGlobal_actual_bound
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ u,‖η u‖≤1)
    (q ρ G H A W : ℝ) (hq₀ : 0≤q) (hq₁ : q≤1)
    (hρ : 0<ρ) (hρ₁ : ρ<1) (hgap : Real.sqrt q<ρ^2)
    (hG : 0<G) (hH : 1≤H) (hA : 0≤A) (hW : 0≤W)
    (hdepth : 100*(5*G+36)<(Fintype.card J:ℝ))
    (hψ : ∀ u,‖ψ u‖≤W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0<d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ))≤Y →
      Y≤Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      ∀ (R : ℕ) (hR : 1≤R) (U Vr : ℝ),
      ‖markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^(G+9)) q U Vr R hR‖≤
        15*((Real.log x)^(-G))^(markedMemoryMomentLength x) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  filter_upwards [markedPhysicalCappedGoodVolumeSum_actual_bound e he hinj ψ η hη hηnorm
    q ρ G H A W hq₀ hq₁ hρ hρ₁ hgap hG hH hA hW hdepth hψ hsupp,
    markedMemoryActualBaselineProduct_bounds e he,marked_array_disjoint_eventually e hinj]
    with x hvolume hbase hdis
  intro d₀ Y hd₀ hYlo hYhi R hR U Vr
  have hraw : ∀ j k,j≠k → Disjoint (markedRawActualPrimeBand e x j) (markedRawActualPrimeBand e x k) := by
    intro j k hjk
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.disjoint_left.mp (hdis hjk))
      ((mem_markedRawPrimeBand _ _).mp hp) ((mem_markedRawPrimeBand _ _).mp hq)
  let b : ℝ := ∏ j,∏ p : markedRawActualPrimeBand e x j,
    markedMemoryBaseline q (markedMemoryMomentLength x) p.1
  let S := markedPhysicalCappedGoodVolumeSum (B := markedDirtyMemoryCutoff x)
    (n := markedMemoryMomentLength x) e x (markedRootTubePrimitive R) hraw
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y
    ((Real.log x)^(G+9)) q U Vr hR (markedRootTubeOrigin R hR)
  have hb : 0≤b ∧ b≤1 := hbase q hq₀ hq₁
  have hS : ‖S‖≤15*((Real.log x)^(-G))^(markedMemoryMomentLength x) :=
    hvolume d₀ Y hd₀ hYlo hYhi R hR U Vr hraw
  have heq : markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^(G+9))
      q U Vr R hR=(b:ℂ)*S :=
    markedPhysicalCoordinateCappedGlobal_eq_goodVolumeSum e x (markedRootTubePrimitive R)
      hraw ψ η d₀ Y ((Real.log x)^(G+9)) q U Vr hR (markedRootTubeOrigin R hR) rfl
  calc
    _ = ‖(b:ℂ)*S‖ := congrArg (fun z : ℂ => ‖z‖) heq
    _ = b*‖S‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb.1]
    _ ≤ ‖S‖ := mul_le_of_le_one_left (norm_nonneg _) hb.2
    _ ≤ _ := hS

theorem markedPhysicalCoordinateCappedGlobal_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ u,‖η u‖≤1)
    (q G H A W : ℝ) (hq₀ : 0≤q) (hq₁ : q<1)
    (hG : 0<G) (hH : 1≤H) (hA : 0≤A) (hW : 0≤W)
    (hdepth : 100*(5*G+36)<(Fintype.card J:ℝ))
    (hψ : ∀ u,‖ψ u‖≤W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0<d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ))≤Y →
      Y≤Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      ∀ (R : ℕ) (hR : 1≤R) (U Vr : ℝ),
      ‖markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^(G+9)) q U Vr R hR‖≤
        15*(Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  obtain ⟨hρ,hρ₁,hgap⟩ := markedMemoryChosenRho_bounds hq₀ hq₁
  filter_upwards [markedPhysicalCoordinateCappedGlobal_actual_bound e he hinj ψ η hη hηnorm
    q (markedMemoryChosenRho q) G H A W hq₀ hq₁.le hρ hρ₁ hgap hG hH hA hW hdepth hψ hsupp,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with x hx hlog
  intro d₀ Y hd₀ hYlo hYhi R hR U Vr
  exact (hx d₀ Y hd₀ hYlo hYhi R hR U Vr).trans_eq
    (congrArg (fun t : ℝ => 15*t)
      (Real.rpow_mul_natCast hlog (-G) (markedMemoryMomentLength x)).symm)

end ArtinMatthews
