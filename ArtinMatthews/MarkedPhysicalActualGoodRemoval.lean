module

public import ArtinMatthews.MarkedPhysicalSourceBad
public import ArtinMatthews.MarkedPhysicalGoodPairingReverse
public import ArtinMatthews.MarkedPhysicalGoodRemovalSplit
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

/-! The exact two-sided cutoff-removal bound for the actual first/second
good predicate and the original physical endpoint vector. -/

noncomputable section
namespace ArtinMatthews

theorem markedPhysicalActualGoodRemoval_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (α β : ℕ → ℂ) (w : Z → ℤ × ℤ) :
    let P := fun j => markedLogPowerBand (e j) x
    let hP := fun j p (hp : p ∈ P j) => (mem_markedLogPowerBand.mp hp).1
    let V := fun j => bandReciprocalMass (P j)
    let pads := ⌊(Real.log x)^(1/100 : ℝ)⌋₊
    let f := fun s : MarkedPhysicalState P (markedPadSlots x) Z =>
      markedPhysicalEndpointVector P (markedPadSlots x) α β s.1.1.1
    let G := MarkedPhysicalActualGood e x d₀ Y w
    ‖markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f f -
      markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalGoodVector G f) (markedPhysicalGoodVector G f)‖ ≤
      markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ ψ η d₀ Y Q 1 (markedPhysicalBadVector G f) f +
      markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q 1
        (markedPhysicalBadVector G f) f := by
  dsimp only
  exact markedPhysicalEdgePairing_good_removal_bound
    (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hdis
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η d₀ Y Q q α β (MarkedPhysicalActualGood e x d₀ Y w)

end ArtinMatthews
