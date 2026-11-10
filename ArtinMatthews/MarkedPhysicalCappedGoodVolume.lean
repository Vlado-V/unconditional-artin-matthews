module

public import ArtinMatthews.MarkedPhysicalHistoryGoodVolume
public import ArtinMatthews.MarkedPhysicalCappedBoundary
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Integrating the original oriented birth-distinct boundary pairing
gives the exact capped decorated sum with literal good volumes. No birth
order, copied-slot factor, source mass or terminal guard is removed. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ) {B R n : ℕ}
  (hZ : ∀ z ∈ markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  (hdis : ∀ j k,j≠k → Disjoint (markedRawActualPrimeBand e x j) (markedRawActualPrimeBand e x k))
  (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q q U Vr : ℝ) (hR : 1≤R) (z₀ : ↥(markedPrimitiveCoordinateTube R))

def markedPhysicalCappedGoodVolumeSum : ℂ :=
  (markedPhysicalMass V (markedPadSlots x):ℂ)*
    ∑ a : MarkedRawActive (markedRawActualPrimeBand e x) (⌊(Real.log x)^(1/100:ℝ)⌋₊+1),
      ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a),
        ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
          markedMemoryIndependentBirthFactorials hZ
            (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
              i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
        markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q
          (markedPhysicalMemoryHistoryIndex (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hZ
            (markedMemoryCappedPathDecoratedAssembly hZ
              hdis (markedMemoryBoundarySource (B := B) z₀ a) i))*
        ((markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr
          (markedPhysicalMemoryHistoryActualIndex e x hZ
            (markedMemoryCappedPathDecoratedAssembly hZ
              hdis (markedMemoryBoundarySource (B := B) z₀ a) i)) hR:ℂ)*
          markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ
            (markedMemoryCappedPathDecoratedAssembly hZ
              hdis (markedMemoryBoundarySource (B := B) z₀ a) i)))

theorem markedPhysicalCappedBoundarySum_integral_goodVolume
    (hn : 0<n) (hz₀ : z₀.1=(1,0)) :
    (∫ p,markedPhysicalCappedBoundarySum (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊) (B := B) (n := n)
      (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      hdis hZ V ψ η d₀ Y Q q z₀
      (fun _ => markedRootMemoryEndpointTest e x d₀ Y U Vr hZ p) ∂markedNormalizedRootMeasure)=
      markedPhysicalCappedGoodVolumeSum (B := B) (n := n) e x hZ hdis V ψ η d₀ Y Q q U Vr hR z₀ := by
  let H (a : MarkedRawActive (markedRawActualPrimeBand e x) (⌊(Real.log x)^(1/100:ℝ)⌋₊+1))
      (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a)) :=
    markedMemoryCappedPathDecoratedAssembly hZ hdis (markedMemoryBoundarySource (B := B) z₀ a) i
  let A (a : MarkedRawActive (markedRawActualPrimeBand e x) (⌊(Real.log x)^(1/100:ℝ)⌋₊+1))
      (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a)) : ℂ :=
    ((markedMemoryPathPrimeChoiceWeight hZ i.1.path q i.1.choices /
      markedMemoryIndependentBirthFactorials hZ
        (markedMemoryCappedPathIndependent (B := B) hZ i.1.path i.1.choices
          i.1.compatible i.1.capacity i.2.1):ℝ):ℂ)*
      markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q
        (markedPhysicalMemoryHistoryIndex (fun j => markedLogPowerBand (e j) x)
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hZ (H a i))
  let F (a : MarkedRawActive (markedRawActualPrimeBand e x) (⌊(Real.log x)^(1/100:ℝ)⌋₊+1))
      (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a)) : ℂ :=
    markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ (H a i))
  let T (a : MarkedRawActive (markedRawActualPrimeBand e x) (⌊(Real.log x)^(1/100:ℝ)⌋₊+1))
      (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a))
      (p : ℝ × (ℝ × ℝ)) : ℂ :=
    markedMemoryStageTestProduct hZ
      (fun k => if markedMemoryAlternatingOrientation k then
        fun u => star (markedRootMemoryEndpointTest e x d₀ Y U Vr hZ p u)
        else markedRootMemoryEndpointTest e x d₀ Y U Vr hZ p) n 0 (H a i)
  have hi (a : MarkedRawActive (markedRawActualPrimeBand e x) (⌊(Real.log x)^(1/100:ℝ)⌋₊+1))
      (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a)) :
      Integrable (fun p => A a i*(T a i p*F a i)) markedNormalizedRootMeasure :=
    markedPhysicalHistoryEndpointTests_weighted_integrable e x d₀ Y U Vr hZ (H a i)
      hz₀ hR hn markedMemoryAlternatingOrientation 0 (A a i) (F a i)
  change (∫ p,(markedPhysicalMass V (markedPadSlots x):ℂ)*∑ a,∑ i,A a i*(T a i p*F a i)
      ∂markedNormalizedRootMeasure)=
    (markedPhysicalMass V (markedPadSlots x):ℂ)*∑ a,∑ i,A a i*
      ((markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr
        (markedPhysicalMemoryHistoryActualIndex e x hZ (H a i)) hR:ℂ)*F a i)
  rw [integral_const_mul,integral_finsetSum _
    (fun a _ => integrable_finsetSum _ (fun i _ => hi a i))]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun i _ => hi a i)]
  apply Finset.sum_congr rfl
  intro i _
  exact markedPhysicalHistoryEndpointTests_weighted_integral e x d₀ Y U Vr hZ (H a i)
    hz₀ hR hn markedMemoryAlternatingOrientation 0 (A a i) (F a i)

theorem markedPhysicalBirthDistinctBoundary_integral_eq_cappedGoodVolume
    (hn : 0<n) (hz₀ : z₀.1=(1,0)) (hV : ∀ j,V j≠0) (ρ : ℝ) (hρ : ρ≠0) :
    (∫ p,markedMemoryBirthDistinctGeometricBoundaryPairing (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊) (B := B) (N := n)
      (markedMemoryTiltAtoms V q n) V hZ ψ η d₀ Y Q ρ markedMemoryAlternatingOrientation
      (markedMemoryHistoryVisitSchedule q n)
      (fun _ => markedRootMemoryEndpointTest e x d₀ Y U Vr hZ p) z₀ ∂markedNormalizedRootMeasure)=
      markedPhysicalCappedGoodVolumeSum (B := B) (n := n) e x hZ hdis V ψ η d₀ Y Q q U Vr hR z₀ := by
  calc
    _ = ∫ p,markedPhysicalCappedBoundarySum (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊) (B := B) (n := n)
        (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        hdis hZ V ψ η d₀ Y Q q z₀
        (fun _ => markedRootMemoryEndpointTest e x d₀ Y U Vr hZ p) ∂markedNormalizedRootMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p =>
        markedPhysicalBirthDistinctBoundary_eq_capped (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊) (B := B) (n := n)
          (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
          hdis hZ V ψ η d₀ Y Q q z₀
          (fun _ => markedRootMemoryEndpointTest e x d₀ Y U Vr hZ p) hV hz₀ ρ hρ)
    _ = _ := markedPhysicalCappedBoundarySum_integral_goodVolume (B := B) (n := n) e x hZ hdis V ψ η
      d₀ Y Q q U Vr hR z₀ hn hz₀

end
end ArtinMatthews
