module

public import ArtinMatthews.MarkedRootGoodBoxCells
public import ArtinMatthews.MarkedRawGoodRootMeasure
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Measurability of the actual finite first/beta test and its transported
moving-box observable, including poles with Lean's literal division. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem markedRawCircleGood_measurable {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y : ℝ) :
    MeasurableSet {θ : AddCircle (1:ℝ) | MarkedRawCircleGood e x a d₀ Y θ} := by
  change MeasurableSet ((markedRawFirstBadRootSet a d₀ Y)ᶜ ∩ {θ | ∀ (I : Finset J) (j : J),
    j ∈ I → (∀ k ∈ I,e k ≤ e j) →
    ¬Real.exp (-((Real.log x)^(e j))/4) ≤
      markedPairFailureProbability (markedRawDirtyFullTrials e x a (I.erase j))
        (markedFreshIntegerProduct (fun k : ↥(Finset.univ \ I) => e k.1) x)
        (markedFreshHarmonicLaw (fun k : ↥(Finset.univ \ I) => e k.1) x)
        (100*Real.exp (-((Real.log x)^(e j)))) θ})
  apply (markedRawFirstBadRootSet_measurable a d₀ Y).compl.inter
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro I
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact (measurableSet_le measurable_const (markedPairFailureProbability_measurable _ _ _ _)).compl

theorem markedRootPhysicalGoodBox_measurable {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y U V : ℝ)
    (z w : Fin 2 → ℝ) :
    MeasurableSet {p | MarkedRootPhysicalGoodBox e x a d₀ Y U V z w p} := by
  have hf : Measurable (markedRootBoxFirst z) := by unfold markedRootBoxFirst markedTau; fun_prop
  have hg : Measurable (markedRootBoxSecond U V z) := by unfold markedRootBoxSecond markedTau; fun_prop
  have hr : Measurable (fun p : ℝ × (ℝ × ℝ) => markedTransportedRatio p.1 z w) := by
    unfold markedTransportedRatio markedTau
    fun_prop
  have hc := (AddCircle.continuous_mk' (1:ℝ)).measurable.comp hr
  exact ((measurableSet_Icc.preimage hf).inter (measurableSet_Icc.preimage hg)).inter
    ((markedRawCircleGood_measurable e x a d₀ Y).preimage hc)

end ArtinMatthews
