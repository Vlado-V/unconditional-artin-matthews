module

public import ArtinMatthews.MarkedPhysicalSourcePolynomialGlobal
public import ArtinMatthews.MarkedPhysicalMomentRootDamping
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The source damping functional is the literal original physical
even moment on the full primitive box, with its original mass. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPhysicalPositionMoment_eq_sourceDamping
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (hx : 1 < x)
    (hdis : Pairwise (fun j k => Disjoint (markedLogPowerBand (e j) x) (markedLogPowerBand (e k) x)))
    (hV : ∀ j,0 < bandReciprocalMass (markedLogPowerBand (e j) x))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U Vr : ℝ)
    (hd₀ : 0 < d₀) (hY : 0 < Y) (hK : 0 ≤ K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) (hU : 1 < U) (hVr : 1 < Vr)
    (S : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) → ℕ) (hS : ∀ a,S a≠0)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr)) → ℤ × ℤ) :
    markedPhysicalPositionMoment (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
      (markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr))
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
      (markedPhysicalRestrictedMatrix (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr))
        (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q
        (MarkedPhysicalActualGood e x d₀ Y w))
      ⌈(Real.log x)^(1/2:ℝ)/2⌉₊ =
    (markedPhysicalSourceDampingGlobal e x ψ η d₀ Y Q q U Vr S hS
      (R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)) w).re := by
  have hn := markedPhysicalMomentLength_pos hx
  have hr : 0 < ⌈(Real.log x)^(1/2:ℝ)/2⌉₊ := by
    unfold markedMemoryMomentLength at hn
    omega
  have hm := markedPhysicalPositionMoment_root_damping
    (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr))
    (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q hdis
    (MarkedPhysicalActualGood e x d₀ Y w) hV ⌈(Real.log x)^(1/2:ℝ)/2⌉₊ hr
    K U Vr hd₀ hY hK hψ hU hVr (Finset.Subset.refl _) S hS
  refine hm.trans ?_
  unfold markedPhysicalSourceDampingGlobal markedPhysicalMomentRootDampingSum
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

end
end ArtinMatthews
