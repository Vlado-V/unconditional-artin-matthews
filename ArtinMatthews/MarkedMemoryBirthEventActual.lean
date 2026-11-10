module

public import ArtinMatthews.MarkedMemoryBirthEventBoundary
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual low-rank event contribution after exact circle averaging.
This is a bound on the original signed oriented chronological history sum,
with the literal performed-address event and empty-memory boundaries. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthEventBoundary_actual_bound
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ i, (1/10:ℝ) ≤ e i) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ u, ‖η u‖ ≤ 1)
    (q ρ G H c T A W : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ < 1) (hgap : Real.sqrt q < ρ^2)
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hdepth : 100*(5*G+26) < (Fintype.card J:ℝ))
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
      (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (z₀ : Z) (N : ℕ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (markedPadSlots x) (markedDirtyMemoryCutoff x) N))
      (orientation : ℕ → Bool),
      0 < d₀ → Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      let C := Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))
      let ε := (Real.log x)^(-G)
      let R := markedRawEdgeCrudeActualConstant (Fintype.card J) (markedRawGhostSchurParameter q ρ) 1 W A 1 *
        (markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*((Real.log x)^(G+7))^3
      let m := markedOperatorModifiedEdgeCount (MarkedMemoryBirthEdgeModified σ) N 0
      ‖markedMemoryBirthEventBoundaryPairing (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊)
        (markedRawActualPrimeAtom e q x) (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))
        hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ orientation (markedMemoryWordVisitQ q N)
        (fun _ => markedRawDirtyGoodCutoff e x r d₀ Y w (fun _ => 1)) σ z₀‖ ≤
        2*C^(N+1)*ε^(N-m)*R^m := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  filter_upwards [markedMemoryBirthPhaseBoundary_actual_bound e he hinj ψ η hη hηnorm q ρ G H c T A W
    hq₀ hq₁ hρ hρ₁ hgap hG hH hc hT hA hW hdepth hψ hsupp] with x hx
  intro Z hZ r d₀ Y w z₀ N σ orientation hd₀ hYlo hYhi hw hτ hbox
  let ν := markedRawActualPrimeAtom e q x
  let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
  let χg := fun _i : ℕ => markedRawDirtyGoodCutoff e x r d₀ Y w
    (fun _s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) (markedDirtyMemoryCutoff x) Z => (1:ℂ))
  let C := Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))
  let ε := (Real.log x)^(-G)
  let R := markedRawEdgeCrudeActualConstant (Fintype.card J) (markedRawGhostSchurParameter q ρ) 1 W A 1 *
    (markedDirtyMemoryCutoff x+1:ℝ)^(Fintype.card J)*((Real.log x)^(G+7))^3
  let m := markedOperatorModifiedEdgeCount (MarkedMemoryBirthEdgeModified σ) N 0
  let U := 2*C^(N+1)*ε^(N-m)*R^m
  change ‖markedMemoryBirthEventBoundaryPairing ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ orientation
    (markedMemoryWordVisitQ q N) χg σ z₀‖ ≤ U
  rw [markedMemoryBirthEventBoundary_eq_integral]
  have hθ : ∀ θ : MarkedMemoryPotentialAddress J (⌊(Real.log x)^(1/100:ℝ)⌋₊+1)
      (markedDirtyMemoryCutoff x) N → AddCircle (1:ℝ),
      ‖markedMemoryBirthPhaseBoundaryPairing (pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊) ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ orientation
      (markedMemoryWordVisitQ q N) χg σ θ z₀‖ ≤ U :=
    fun θ => hx Z hZ r d₀ Y w z₀ N σ θ orientation hd₀ hYlo hYhi hw hτ hbox
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ := Measure.pi (fun _ : MarkedMemoryPotentialAddress J (⌊(Real.log x)^(1/100:ℝ)⌋₊+1) (markedDirtyMemoryCutoff x) N =>
        @AddCircle.haarAddCircle (1:ℝ) inferInstance)) (Filter.Eventually.of_forall hθ)

end ArtinMatthews
