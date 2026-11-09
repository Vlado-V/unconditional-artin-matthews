module

public import ArtinMatthews.MarkedPhysicalCappedGlobalPath
public import ArtinMatthews.MarkedPhysicalCappedGoodVolumeFlatten


set_option backward.privateInPublic true
@[expose] public section

/-! Exact actual coordinate-to-history main-term identification. The
full-band baseline is explicit; physical sigma, tilted source atoms,
copied-slot probabilities and the original small memory cap are retained. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

theorem markedPhysicalCoordinateCappedGlobal_eq_goodVolumeSum
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {R : ℕ}
    (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
    (hdis : ∀ j k,j≠k → Disjoint (markedRawActualPrimeBand e x j) (markedRawActualPrimeBand e x k))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q U Vr : ℝ)
    (hR : 1≤R) (z₀ : ↥(markedPrimitiveCoordinateTube R)) (hz₀ : z₀.1=(1,0)) :
    markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y Q q U Vr R hR=
      ((∏ j,∏ p : markedRawActualPrimeBand e x j,
        markedMemoryBaseline q (markedMemoryMomentLength x) p.1:ℝ):ℂ)*
      markedPhysicalCappedGoodVolumeSum (B := markedDirtyMemoryCutoff x) (n := markedMemoryMomentLength x)
        e x hZ hdis (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        ψ η d₀ Y Q q U Vr hR z₀ := by
  rw [markedPhysicalCoordinateCappedGlobal_path e x ψ η d₀ Y Q q U Vr R hR z₀ hz₀ hZ,
    markedPhysicalCappedGoodVolumeSum_path]

end
end ArtinMatthews
