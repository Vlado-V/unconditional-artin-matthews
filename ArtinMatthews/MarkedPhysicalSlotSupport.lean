module

public import ArtinMatthews.MarkedPhysicalHilbertMatrix
public import ArtinMatthews.MarkedFiniteSingleSlotExchange
public import ArtinMatthews.MarkedPhysicalRawMatrixEntry
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

/-! The actual copied-prefix and full-cross-ban tests imply the genuine
single-slot exchange after the two physical slot permutations. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedRawJoint_ne_zero_not_banned
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z)
    (h : markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t≠0) :
    ¬MarkedRawFullCrossBan s.2.1 ((markedRawActiveSplit pads) t.2.1).2 := by
  unfold markedRawEdgeJointCoefficient at h
  dsimp only at h
  split_ifs at h with hd hv hb
  · exact False.elim (h rfl)
  · exact hb
  · exact False.elim (h rfl)
  · exact False.elim (h rfl)

theorem markedPhysicalPermutedEdge_exchange
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z)
    (σ τ : J → Equiv.Perm (Fin (pads+1)))
    (h : markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q
      (markedPhysicalSlotEquiv P (pads+1) Z σ s) (markedPhysicalSlotEquiv P (pads+1) Z τ t)≠0) :
    let a := (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
    let b := (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1
    (∀ j,¬∃ k,a j k=b j (τ j (Fin.last pads))) ∧
      (∀ j x,(∃ k,b j k=x) ↔
        ((∃ k,a j k=x) ∧ x≠a j (σ j (Fin.last pads))) ∨ x=b j (τ j (Fin.last pads))) := by
  let a := (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
  let b := (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1
  change (∀ j,¬∃ k,a j k=b j (τ j (Fin.last pads))) ∧ _
  have hh := markedPhysicalEdgeMatrix_ne_zero_guards P hP V pads Z hZ ψ η d₀ Y Q q
    (markedPhysicalSlotEquiv P (pads+1) Z σ s) (markedPhysicalSlotEquiv P (pads+1) Z τ t) h
  dsimp only at hh
  have hcopy (j : J) (k : Fin pads) : a j (σ j k.castSucc)=b j (τ j k.castSucc) :=
    congrFun (congrFun hh.1 j) k
  have hban := markedRawJoint_ne_zero_not_banned hZ ψ η d₀ Y Q 1 (fun _ => 1) _ _ hh.2
  constructor
  · intro j hbad
    obtain ⟨k,hk⟩ := hbad
    apply hban
    refine ⟨j,j,(σ j).symm k,?_⟩
    change (b j (τ j (Fin.last pads))).1=(a j (σ j ((σ j).symm k))).1
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val hk.symm
  · intro j x
    exact markedPermutedSingleSlotExchange pads (a j) (b j)
      (markedPhysicalStateToRaw_distinct P hP (pads+1) Z s j) (σ j) (τ j) (hcopy j) x

end
end ArtinMatthews
