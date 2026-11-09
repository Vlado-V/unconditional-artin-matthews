module

public import ArtinMatthews.MarkedRootWindowCutoff
public import ArtinMatthews.MarkedMemoryBirthDistinctActual
public import ArtinMatthews.MarkedPrimitiveCoordinateTube


set_option backward.privateInPublic true
@[expose] public section

/-! Apply the proved signed birth-distinct estimate to the actual finite
root-box window. All geometry hypotheses are discharged uniformly in the
normalized root point, the tube radius and both physical box scales. -/

noncomputable section
namespace ArtinMatthews
open Filter
attribute [local instance] Classical.propDecidable

theorem markedRootTubePrimitive (R : ℕ) :
    ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2 :=
  fun z hz => ((markedPrimitiveCoordinateTube_mem R z).mp hz).2.2

def markedRootWindowOrigin (R : ℕ) (hR : 1≤R) (U V : ℝ)
    (p : ℝ × (ℝ × ℝ)) (hp : p∈markedRootBoxDomain) :
    markedRootStateWindow (markedPrimitiveCoordinateTube R) U V p := by
  refine ⟨(1,0),markedRootStateWindow_origin _ U V p hp ?_⟩
  apply (markedPrimitiveCoordinateTube_mem R (1,0)).mpr
  refine ⟨?_,?_,by norm_num⟩
  · simpa only [abs_one] using (show (1:ℤ)≤R by exact_mod_cast hR)
  · simpa only [abs_zero] using (Nat.cast_nonneg R : (0:ℤ)≤R)

def markedRootWindowGoodBoundary
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q ρ : ℝ)
    (R : ℕ) (hR : 1≤R) (U V : ℝ) (p : ℝ × (ℝ × ℝ)) (hp : p∈markedRootBoxDomain)
    (orientation : ℕ → Bool) : ℂ :=
  let Z := markedRootStateWindow (markedPrimitiveCoordinateTube R) U V p
  let hZ := markedRootStateWindow_primitive U V (markedRootTubePrimitive R) p
  markedMemoryBirthDistinctGeometricBoundaryPairing (N := markedMemoryMomentLength x)
    (B := markedDirtyMemoryCutoff x) (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
    (markedRawActualPrimeAtom e q x) (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    hZ ψ η d₀ Y Q ρ orientation (markedMemoryWordVisitQ q (markedMemoryMomentLength x))
    (fun _ => markedRawDirtyGoodCutoff e x p.1 d₀ Y
      (fun z : Z => markedPrimitiveCoordinateCompletion z.1 (hZ _ z.2)) (fun _ => 1))
    (markedRootWindowOrigin R hR U V p hp)

set_option backward.isDefEq.respectTransparency false in
theorem markedRootWindowGoodBoundary_actual_bound
    {J : Type*} [Fintype J] [DecidableEq J]
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
      ∀ (R : ℕ) (hR : 1≤R) (U V : ℝ) (p : ℝ × (ℝ × ℝ))
        (hp : p∈markedRootBoxDomain) (orientation : ℕ → Bool),
      ‖markedRootWindowGoodBoundary e x ψ η d₀ Y ((Real.log x)^(G+9)) q ρ
        R hR U V p hp orientation‖≤((Real.log x)^(-G))^(markedMemoryMomentLength x) := by
  filter_upwards [markedMemoryBirthDistinct_actual_bound e he hinj ψ η hη hηnorm
    q ρ G H (1/16) 16 A W hq₀ hq₁ hρ hρ₁ hgap hG hH (by norm_num) (by norm_num)
    hA hW hdepth hψ hsupp] with x hx
  intro d₀ Y hd₀ hYlo hYhi R hR U V p hp orientation
  let Z := markedRootStateWindow (markedPrimitiveCoordinateTube R) U V p
  let hZ := markedRootStateWindow_primitive U V (markedRootTubePrimitive R) p
  have hτ : ∀ z∈Z,(1/16:ℝ)≤|markedMinorIntegerTau p.1 z| ∧ |markedMinorIntegerTau p.1 z|≤16 := by
    intro z hz
    have hb := markedRootStateWindow_tau_bounds (markedPrimitiveCoordinateTube R) U V p hp ⟨z,hz⟩
    rw [abs_of_nonneg (le_trans (by norm_num) hb.1)]
    exact hb
  exact hx Z hZ p.1 d₀ Y
    (fun z => markedPrimitiveCoordinateCompletion z.1 (hZ _ z.2))
    (markedRootWindowOrigin R hR U V p hp) orientation hd₀ hYlo hYhi
    (fun z => markedPrimitiveCoordinateCompletion_det z.1 (hZ _ z.2)) hτ
    (markedRootStateWindow_tau_ratio (markedPrimitiveCoordinateTube R) U V p hp)

end ArtinMatthews
