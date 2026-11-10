module

public import ArtinMatthews.MarkedPrimitiveCoordinateCompletion
public import ArtinMatthews.MarkedRawGoodRootTransport
public import ArtinMatthews.MarkedMemoryHistoryGhostChoice
public import ArtinMatthews.MarkedRootGoodBoxCells
public import ArtinMatthews.MarkedRawGoodSlots
public import ArtinMatthews.MarkedRootGoodBoxMeasure
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

/-! The literal ordered endpoint cutoff in normalized root coordinates.
It retains the physical box, the actual first/beta test and the true
coordinate completion. The ambient root domain is kept explicitly. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x d₀ Y U V : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)

def MarkedRootMemoryEndpointGood (p : ℝ × (ℝ × ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) : Prop :=
  p ∈ markedRootBoxDomain ∧
    MarkedRootPhysicalBox U V (markedRootIntegerVector s.1.1) p ∧
    MarkedRawDirtyGood e x p.1 d₀ Y
      (fun z => markedPrimitiveCoordinateCompletion z.1 (hZ _ z.2)) s

def markedRootMemoryEndpointTest (p : ℝ × (ℝ × ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) : ℂ :=
  if MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p s then 1 else 0

theorem markedRootMemoryEndpointGood_iff (p : ℝ × (ℝ × ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) :
    MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p s ↔
      p ∈ markedRootBoxDomain ∧
        MarkedRootPhysicalGoodBox e x s.2.1 d₀ Y U V
          (markedRootIntegerVector s.1.1)
          (markedRootIntegerVector (markedPrimitiveCoordinateCompletion s.1.1 (hZ _ s.1.2))) p := by
  rw [MarkedRootMemoryEndpointGood,markedRawDirtyGood_iff_circle]
  rfl

theorem markedRootMemoryEndpointGood_slots (p : ℝ × (ℝ × ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z)
    (σ : J → Equiv.Perm (Fin M)) :
    MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p (markedRawSlotEquiv σ s) ↔
      MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p s := by
  unfold MarkedRootMemoryEndpointGood
  exact and_congr Iff.rfl (and_congr Iff.rfl (markedRawDirtyGood_slots e x p.1 d₀ Y _ s σ))

theorem markedRootMemoryEndpointGood_ghost (p : ℝ × (ℝ × ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z)
    (g : MarkedMemoryGhostChoice hZ s) :
    MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p (markedMemoryGhostChoiceTarget hZ s g) ↔
      MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p s := Iff.rfl

theorem markedRootMemoryEndpointTest_star (p : ℝ × (ℝ × ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) :
    star (markedRootMemoryEndpointTest e x d₀ Y U V hZ p s)=
      markedRootMemoryEndpointTest e x d₀ Y U V hZ p s := by
  unfold markedRootMemoryEndpointTest
  split_ifs <;> simp only [star_one,star_zero]

theorem markedRootMemoryEndpointTest_norm_le (p : ℝ × (ℝ × ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) :
    ‖markedRootMemoryEndpointTest e x d₀ Y U V hZ p s‖ ≤ 1 := by
  unfold markedRootMemoryEndpointTest
  split_ifs <;> norm_num

theorem markedRootMemoryEndpointGood_measurable
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) :
    MeasurableSet {p | MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p s} := by
  simp_rw [markedRootMemoryEndpointGood_iff]
  exact (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)).inter
    (markedRootPhysicalGoodBox_measurable e x s.2.1 d₀ Y U V _ _)

end
end ArtinMatthews
