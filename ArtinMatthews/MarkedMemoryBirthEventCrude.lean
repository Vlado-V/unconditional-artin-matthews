module

public import ArtinMatthews.MarkedMemoryBirthAtom
public import ArtinMatthews.MarkedMemoryBirthEventBoundary
public import ArtinMatthews.MarkedMemoryBirthEventMemo
public import ArtinMatthews.MarkedMemoryPositiveBoundaryActual
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

/-! The original oriented permutation-event boundary has the full
rank-many atom saving. All conditional rows and chronological memo
requirements are discharged in this actual finite statement. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthEventBoundary_actual_atom_bound
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B N : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (r d₀ Y Q H W A : ℝ) (w : Z → ℤ × ℤ)
      (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (z₀ : Z)
      (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
      (χ : ℕ → MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ),
      1 ≤ Y → 1 ≤ Q → 0 ≤ H → 0 ≤ W → 0 ≤ A →
      (∀ u,‖η u‖ ≤ H) → (∀ u,‖ψ u‖ ≤ W) → (∀ u,ψ u≠0 → |u| ≤ A) →
      (∀ z,markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z : Z,markedMinorIntegerTau r z.1≠0) →
      (∀ z v : Z,|markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ j,0 ≤ qStage j ∧ qStage j ≤ Real.sqrt q) → (∀ j s,‖χ j s‖ ≤ 1) →
      let ν := markedRawActualPrimeAtom e q x
      let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
      let v₀ := markedRawGhostSchurParameter q ρ
      let Cg := Real.exp ((Fintype.card J:ℝ)*(2*v₀/ρ))
      let R := markedRawEdgeCrudeActualConstant (Fintype.card J) v₀ H W A 1*(B+1:ℝ)^(Fintype.card J)*Q^3
      ‖markedMemoryBirthEventBoundaryPairing ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀‖ ≤
        (2:ℝ)^(Fintype.card J*(pads+1))*Cg^(N+1)*R^N*
          (markedMemoryBirthAtomEnvelope x)^(markedBirthPermutationRank σ) := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  filter_upwards [markedMemoryPositivePivotBoundary_actual_bound e he hq₀ hq₁ hρ hρ₁ hgap,
    markedMemoryBirthAtom_actual_eventually e he] with x hb hatom
  intro pads B N Z hZ ψ η r d₀ Y Q H W A w σ z₀ orientation qStage χ
    hY hQ hH hW hA hη hψ hsupp hw hτ hbox hstage hχ
  dsimp only
  have hν : ∀ j p,0 ≤ markedRawActualPrimeAtom e q x j p :=
    fun j p => (hatom q hq₀ hq₁ j p).1
  exact (markedMemoryBirthEventBoundary_le_positive_actual (markedRawActualPrimeAtom e q x) hν
    (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) hZ ψ η d₀ Y Q ρ
    orientation qStage χ σ z₀).trans
      (hb pads B N Z hZ ψ η r d₀ Y Q H W A w σ z₀ orientation qStage χ
        hY hQ hH hW hA hη hψ hsupp hw hτ hbox hstage hχ)

end ArtinMatthews
