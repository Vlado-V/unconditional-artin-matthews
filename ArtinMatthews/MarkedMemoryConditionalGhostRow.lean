module

public import ArtinMatthews.MarkedMemoryHistoryGhostChoice
public import ArtinMatthews.MarkedMinorArcRawGhostConditional
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Basify
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

/-! The conditional ghost row on the literal chronological choice
structure is exactly the already proved raw deletion/batch row. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryConditionalGhostRow
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ v₀ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (s : MarkedRawState P M B Z)
    (gate : (del : MarkedRawGhostDeletion s.2.2) → (l : MarkedRawGhostBirthSizes s.2.2 del) →
      MarkedRawGhostBirthLabels l → Prop) : ℝ :=
  ∑ c : MarkedMemoryGhostChoice hZ s, if gate c.deletion c.sizes c.births then
    ‖markedMemoryGhostChoiceWeight ν V qStage ρ hZ s c‖*
      (markedRawMemorySchurWeight v₀ (markedMemoryGhostChoiceTarget hZ s c).2.2/
        markedRawMemorySchurWeight v₀ s.2.2)
  else 0

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryConditionalGhostRow_eq
    {J : Type*} [Fintype J] [decJ : DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ v₀ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (s : MarkedRawState P M B Z)
    (gate : (del : MarkedRawGhostDeletion s.2.2) → (l : MarkedRawGhostBirthSizes s.2.2 del) →
      MarkedRawGhostBirthLabels l → Prop) :
    markedMemoryConditionalGhostRow ν V qStage ρ v₀ hZ s gate =
      markedRawGhostConditionalWeightedAbsRow ν V qStage ρ v₀ s.2.2 s.1.1 (hZ _ s.1.2) gate := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  unfold markedMemoryConditionalGhostRow
  rw [← Equiv.sum_comp (markedMemoryGhostChoiceEquiv hZ s).symm]
  simp only [Fintype.sum_sigma,markedMemoryGhostChoiceWeight,markedMemoryGhostChoiceTarget,
    markedMemoryGhostChoiceEquiv,Equiv.coe_fn_symm_mk,Complex.norm_real,Real.norm_eq_abs]
  unfold markedRawGhostConditionalWeightedAbsRow
  let F (del : MarkedRawGhostDeletion s.2.2) : ℝ :=
    ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l,
      if gate del l births then
        |markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
          markedRawGhostBirthMass ν l births| *
          (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2) del l births)/
            markedRawMemorySchurWeight v₀ s.2.2) else 0
  let allowed := MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2)
  change (∑ del : {d // allowed d},F del.1)=∑ del,if allowed del then F del else 0
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter allowed) (by simp) F).symm

end ArtinMatthews
