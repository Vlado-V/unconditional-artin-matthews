module

public import ArtinMatthews.IdealProbeProjection
public import ArtinMatthews.IdealHoeffdingProjection
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
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The sum of all non-full probe components is a contraction. This
keeps the exceptional raw terms grouped before taking absolute values. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealHoeffdingTransform_sub {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (f g : MarkedPhysicalMarking P M → ℂ) :
    idealHoeffdingTransform P b (fun a => f a-g a)=fun t =>
      idealHoeffdingTransform P b f t-idealHoeffdingTransform P b g t := by
  have he : idealWeightedVector P (fun a => f a-g a)=idealWeightedVector P f-idealWeightedVector P g := by
    apply WithLp.ofLp_injective
    funext a
    change (Real.sqrt (idealLabelMass P M a):ℂ)*(f a-g a)=
      (Real.sqrt (idealLabelMass P M a):ℂ)*f a-(Real.sqrt (idealLabelMass P M a):ℂ)*g a
    ring
  funext t
  unfold idealHoeffdingTransform
  rw [he,map_sub]
  rfl

def idealProbeRemainder {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (probes tail : Finset (J × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) : MarkedPhysicalMarking P M → ℂ :=
  fun a => idealAverageSet P tail f a-idealProbeProjection P probes tail f a

theorem idealProbeRemainder_transform {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes tail : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealHoeffdingTransform P b (idealProbeRemainder P probes tail f)=fun t =>
      if Disjoint (idealFullSupport a₀ t) tail ∧ ¬probes ⊆ idealFullSupport a₀ t
      then idealHoeffdingTransform P b f t else 0 := by
  unfold idealProbeRemainder
  rw [idealHoeffdingTransform_sub,
    idealHoeffdingTransform_average P hV hw b a₀ hb,
    idealProbeProjection_transform P hV hw b a₀ hb]
  funext t
  simp only [idealAverageSurvives_iff]
  by_cases ht : Disjoint (idealFullSupport a₀ t) tail <;>
    by_cases hp : probes ⊆ idealFullSupport a₀ t <;> simp [ht,hp]

theorem idealProbeRemainder_energy_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hw : ∀ j p,0 < markedHarmonicAtom (P j) p)
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (a₀ : ∀ j,↥(P j)) (hb : ∀ j,b j (a₀ j)=idealProbabilityRoot (markedHarmonicAtom (P j)))
    (probes tail : Finset (J × Fin M)) (f : MarkedPhysicalMarking P M → ℂ) :
    idealLabelEnergy P M (idealProbeRemainder P probes tail f) ≤ idealLabelEnergy P M f := by
  rw [← idealHoeffdingTransform_energy P hV b,
    idealProbeRemainder_transform P hV hw b a₀ hb,← idealHoeffdingTransform_energy P hV b f]
  apply sum_le_sum
  intro t _
  dsimp only
  split_ifs with h
  · rfl
  · simp

end
end ArtinMatthews
