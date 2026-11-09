module

public import ArtinMatthews.MarkedPhysicalCoordinateGoodVolume
public import ArtinMatthews.MarkedMemoryPathCapacityGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! Literal independent-line, capped and omitted-cap contributions on
the actual fixed coordinate carrier. These are separate from the
root-replacement step and retain the source physical loop and lists. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q : ℝ) {n B : ℕ}
  (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n B)
  (hB : 1≤B)

def markedPhysicalCoordinatePathApply
    (F : MarkedMemoryActivePathData (markedRawActualPrimeBand e x)
      ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPrimitiveCoordinateTube B) n → ℂ → ℂ) : ℂ :=
  if ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v) then
    if hc : markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i≠0 then
      if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) then
        F (markedPhysicalCoordinateIndexActivePath (fun j => markedLogPowerBand (e j) x)
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i hB ha hc)
          (markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i)
      else 0
    else 0
  else 0

def markedPhysicalCoordinateIndependentTerm (q U W : ℝ) : ℂ :=
  markedPhysicalCoordinatePathApply e x V ψ η d₀ Y Q i hB (fun d c =>
    (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB:ℂ)*
      ((markedMemoryPathIndependentExpectation
        (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2) d q:ℂ)*c))

def markedPhysicalCoordinateCappedTerm (q U W : ℝ) (cap : ℕ) : ℂ :=
  markedPhysicalCoordinatePathApply e x V ψ η d₀ Y Q i hB (fun d c =>
    (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB:ℂ)*
      markedMemoryPathCappedLineContribution
        (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2) d q cap c)

def markedPhysicalCoordinateCapacityTerm (q U W : ℝ) (cap : ℕ) : ℂ :=
  markedPhysicalCoordinatePathApply e x V ψ η d₀ Y Q i hB (fun d c =>
    (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB:ℂ)*
      markedMemoryPathCapacityCorrection
        (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2) d q cap c)

theorem markedPhysicalCoordinateLineTerm_cap_split (q U W : ℝ) (cap : ℕ)
    (hdis : ∀ j k,j≠k → Disjoint (markedRawActualPrimeBand e x j) (markedRawActualPrimeBand e x k))
    (hb : ∀ j (p : markedRawActualPrimeBand e x j),markedMemoryBaseline q n p.1≠0) :
    markedPhysicalCoordinateIndependentTerm e x V ψ η d₀ Y Q i hB q U W=
      markedPhysicalCoordinateCappedTerm e x V ψ η d₀ Y Q i hB q U W cap+
      markedPhysicalCoordinateCapacityTerm e x V ψ η d₀ Y Q i hB q U W cap := by
  unfold markedPhysicalCoordinateIndependentTerm markedPhysicalCoordinateCappedTerm
    markedPhysicalCoordinateCapacityTerm markedPhysicalCoordinatePathApply
  split_ifs with ha hc hloop
  · dsimp only
    let d := markedPhysicalCoordinateIndexActivePath (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i hB ha hc
    let c := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
    let v : ℂ := (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB:ℂ)
    have h := markedMemoryPathLineContribution_cap_split
      (fun z hz => ((markedPrimitiveCoordinateTube_mem B z).mp hz).2.2) d q cap hdis hb c
    exact (congrArg (fun w : ℂ => v*w) h).trans (mul_add _ _ _)
  all_goals simp only [add_zero]

end
end ArtinMatthews
