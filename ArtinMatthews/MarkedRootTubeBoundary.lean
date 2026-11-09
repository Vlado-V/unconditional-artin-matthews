module

public import ArtinMatthews.MarkedRootWindowBoundaryActual
public import ArtinMatthews.MarkedMemoryBirthDistinctWindow
public import ArtinMatthews.MarkedPhysicalCappedGoodVolume


set_option backward.privateInPublic true
@[expose] public section

/-! Exact zero-extension identification for the actual physical root
endpoint cutoff. The large tube boundary equals the signed good word
on its literal finite root-box window. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedRootTubeOrigin (R : ℕ) (hR : 1≤R) : markedPrimitiveCoordinateTube R := by
  refine ⟨(1,0),(markedPrimitiveCoordinateTube_mem R (1,0)).mpr ?_⟩
  refine ⟨?_,?_,by norm_num⟩
  · simpa only [abs_one] using (show (1:ℤ)≤R by exact_mod_cast hR)
  · simpa only [abs_zero] using (Nat.cast_nonneg R : (0:ℤ)≤R)

def markedRootTubeBoundary
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q ρ : ℝ)
    (R : ℕ) (hR : 1≤R) (U V : ℝ) (p : ℝ × (ℝ × ℝ))
    (orientation : ℕ → Bool) : ℂ :=
  markedMemoryBirthDistinctGeometricBoundaryPairing (N := markedMemoryMomentLength x)
    (B := markedDirtyMemoryCutoff x) (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
    (markedMemoryTiltAtoms (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) q
      (markedMemoryMomentLength x))
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedRootTubePrimitive R)
    ψ η d₀ Y Q ρ orientation (markedMemoryHistoryVisitSchedule q (markedMemoryMomentLength x))
    (fun _ => markedRootMemoryEndpointTest e x d₀ Y U V (markedRootTubePrimitive R) p)
    (markedRootTubeOrigin R hR)

set_option backward.isDefEq.respectTransparency false in
theorem markedRootTubeBoundary_eq_window
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q ρ : ℝ)
    (R : ℕ) (hR : 1≤R) (U V : ℝ) (p : ℝ × (ℝ × ℝ)) (hp : p∈markedRootBoxDomain)
    (orientation : ℕ → Bool) :
    markedRootTubeBoundary e x ψ η d₀ Y Q q ρ R hR U V p orientation=
      markedRootWindowGoodBoundary e x ψ η d₀ Y Q q ρ R hR U V p hp orientation := by
  let Z := markedRootStateWindow (markedPrimitiveCoordinateTube R) U V p
  let h := markedRootStateWindow_subset (markedPrimitiveCoordinateTube R) U V p
  let hZ := markedRootStateWindow_primitive U V (markedRootTubePrimitive R) p
  let χ : ℕ → MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x)
      (markedDirtyMemoryCutoff x) (markedPrimitiveCoordinateTube R) → ℂ :=
    fun _ => markedRootMemoryEndpointTest e x d₀ Y U V (markedRootTubePrimitive R) p
  have hχ : ∀ j s,s.1.1∉Z → χ j s=0 := by
    intro j s hs
    exact markedRootMemoryEndpointTest_eq_zero_of_outside e x d₀ Y U V (markedRootTubePrimitive R) p s hs
  have hh := markedMemoryBirthDistinct_boundary_restrict h hZ (markedRootTubePrimitive R)
    (markedMemoryTiltAtoms (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) q
      (markedMemoryMomentLength x))
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q ρ orientation
    (markedMemoryHistoryVisitSchedule q (markedMemoryMomentLength x)) χ hχ
    (markedMemoryMomentLength x) (markedRootWindowOrigin R hR U V p hp)
  have heq : (fun j s => χ j (markedRawStateInclude h s))=
      (fun _ => markedRawDirtyGoodCutoff e x p.1 d₀ Y
        (fun z : Z => markedPrimitiveCoordinateCompletion z.1 (hZ _ z.2)) (fun _ => 1)) := by
    funext j s
    exact markedRootMemoryEndpointTest_window e x d₀ Y U V (markedRootTubePrimitive R) p hp s
  have hsmall := congrArg
    (fun cutoff : ℕ → MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x)
        (markedDirtyMemoryCutoff x) Z → ℂ =>
      markedMemoryBirthDistinctGeometricBoundaryPairing (B := markedDirtyMemoryCutoff x)
        (N := markedMemoryMomentLength x) (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
        (markedMemoryTiltAtoms (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) q
          (markedMemoryMomentLength x))
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hZ ψ η d₀ Y Q ρ orientation
        (markedMemoryHistoryVisitSchedule q (markedMemoryMomentLength x)) cutoff
        (markedRootWindowOrigin R hR U V p hp)) heq
  exact hh.trans hsmall

end ArtinMatthews
