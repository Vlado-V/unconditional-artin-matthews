module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternFilteredRows
public import ArtinMatthews.MarkedMinorArcRawEdgePatternMinorRows
public import ArtinMatthews.MarkedMinorArcDirtyPatternSwap
public import ArtinMatthews.MarkedMinorArcRawEdgePatternAveragedEnergy
public import ArtinMatthews.MarkedMinorArcRawEdgePatternRowPartition
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The two asymmetric dirty-sector energy bounds. All four hypotheses
are arithmetic rows on the original charge; reversal and its correction
factor are proved here, not assumed as column bounds. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawEdge_dirty_sector_energy_of_rows
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ Λ ε C : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ z a,MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (hv₀ : 0 < v₀) (hΛ : 1 ≤ Λ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hSwap : ∀ p q : J → Bool,‖markedRawEdgeFlagChargeSwap V p q‖ ≤ Λ)
    (hprom : ∀ β : MarkedRawEdgePatternKernel P pads B Z,
      (∀ p q s t,‖β p q s t‖ ≤ Λ) → ∀ s,
      markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν
        (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
        (markedRawEdgePromotedKernel (fun p q u v => β p q u v *
          markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v)) v₀) s ≤ ε)
    (hnop : ∀ β : MarkedRawEdgePatternKernel P pads B Z,
      (∀ p q s t,‖β p q s t‖ ≤ Λ) → ∀ s,
      markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν
        (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
        (markedRawEdgeNoPromotionKernel (fun p q u v => β p q u v *
          markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v)) v₀) s ≤ C)
    (hpromR : ∀ β : MarkedRawEdgePatternKernel P pads B Z,
      (∀ p q s t,‖β p q s t‖ ≤ Λ) → ∀ s,
      markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν
        (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
        (markedRawEdgePromotedKernel (fun p q u v => β p q u v *
          markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ u v)) v₀) s ≤ ε)
    (hnopR : ∀ β : MarkedRawEdgePatternKernel P pads B Z,
      (∀ p q s t,‖β p q s t‖ ≤ Λ) → ∀ s,
      markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν
        (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
        (markedRawEdgeNoPromotionKernel (fun p q u v => β p q u v *
          markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ u v)) v₀) s ≤ C)
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z a,MarkedRawMemorySymmetric (fun m => f (z,(a,m)))) :
    (∑ s,markedRawStateMass ν s * ‖markedRawEdgePatternSymmetrized ν
      (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
      (markedRawEdgePromotedKernel (fun _ _ => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ)) f s‖^2) ≤
        ε*(ε+C)*(∑ s,markedRawStateMass ν s*‖f s‖^2) ∧
    (∑ s,markedRawStateMass ν s * ‖markedRawEdgePatternSymmetrized ν
      (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ
      (markedRawEdgeStoreOnlyKernel (fun _ _ => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ)) f s‖^2) ≤
        C*ε*(∑ s,markedRawStateMass ν s*‖f s‖^2) := by
  classical
  let K : MarkedRawEdgePatternKernel P pads B Z := fun _ _ =>
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ
  let bp : MarkedRawEdgePatternKernel P pads B Z := fun p _ _ _ =>
    if p = (fun _ => false) then 0 else 1
  let bs : MarkedRawEdgePatternKernel P pads B Z := fun p q _ _ =>
    if p = (fun _ => false) ∧ q ≠ (fun _ => false) then 1 else 0
  let bt : MarkedRawEdgePatternKernel P pads B Z := fun _ q _ _ =>
    if q = (fun _ => false) then 0 else 1
  let βp : MarkedRawEdgePatternKernel P pads B Z := fun p q u v =>
    markedRawEdgeFlagChargeSwap V p q * markedRawEdgePatternReverse bp p q u v
  let βn : MarkedRawEdgePatternKernel P pads B Z := fun p q _ _ =>
    if q = (fun _ => false) then markedRawEdgeFlagChargeSwap V p q else 0
  have hΛ₀ : 0 ≤ Λ := zero_le_one.trans hΛ
  have hβp : ∀ p q s t,‖βp p q s t‖ ≤ Λ := by
    intro p q s t
    by_cases hq : q = fun _ => false
    · simpa [βp,bp,markedRawEdgePatternReverse,hq] using hΛ₀
    · simpa [βp,bp,markedRawEdgePatternReverse,hq] using hSwap p q
  have hβn : ∀ p q s t,‖βn p q s t‖ ≤ Λ := by
    intro p q s t
    by_cases hq : q = fun _ => false
    · simpa [βn,hq] using hSwap p q
    · simpa [βn,hq] using hΛ₀
  have hbt : ∀ p q s t,‖bt p q s t‖ ≤ Λ := by
    intro p q s t
    by_cases hq : q = fun _ => false
    · simpa [bt,hq] using hΛ₀
    · simpa [bt,hq] using hΛ
  have hAP : markedRawEdgePromotedKernel K =
      (fun p q s t => bp p q s t * markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t) := by
    funext p q s t
    by_cases hp : p = fun _ => false <;> simp [K,bp,markedRawEdgePromotedKernel,markedRawEdgeFlagGate,hp]
  have hAS : markedRawEdgeStoreOnlyKernel K =
      (fun p q s t => bs p q s t * markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t) := by
    funext p q s t
    by_cases h : p = (fun _ => false) ∧ q ≠ (fun _ => false) <;>
      simp [K,bs,markedRawEdgeStoreOnlyKernel,markedRawEdgeFlagGate,h]
  have hpromRow : ∀ s,markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν
      (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ (markedRawEdgePromotedKernel K) v₀) s ≤ ε := by
    intro s
    simpa only [one_mul] using hprom (fun _ _ _ _ => 1) (by intro p q u v; simpa using hΛ) s
  have hstoreRow : ∀ s,markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν
      (fun j => ((V j)⁻¹:ℝ)) (fun _ => 1) hZ (markedRawEdgeStoreOnlyKernel K) v₀) s ≤ C := by
    intro s
    have hKS : markedRawEdgeStoredKernel K =
        (fun p q u v => bt p q u v * markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v) := by
      funext p q u v
      by_cases hq : q = fun _ => false <;> simp [K,bt,markedRawEdgeStoredKernel,markedRawEdgeFlagGate,hq]
    rw [markedRawEdgeStoreOnlyKernel_eq_noPromotion_stored,hKS]
    exact hnop bt hbt s
  have hpromCol : ∀ s,markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν
      (fun _ => 1) (fun j => ((V j)⁻¹:ℝ)) hZ
      (markedRawEdgePatternReverse (markedRawEdgePromotedKernel K)) v₀) s ≤ ε+C := by
    intro s
    rw [hAP,markedRawEdgePatternWeightedAverage_minor_reverse ν _ _ hdisj hZ ψ η d₀ Y Q ρ v₀ χ bp,
      markedRawEdgePatternWeightedAverage_minor_swap ν V (fun j => (hV j).ne') hZ
        (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ v₀ χ (markedRawEdgePatternReverse bp)]
    rw [markedRawEdgePatternWeightedRow_average_promotion_split]
    exact add_le_add (hpromR βp hβp s) (hnopR βp hβp s)
  have hstoreCol : ∀ s,markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν
      (fun _ => 1) (fun j => ((V j)⁻¹:ℝ)) hZ
      (markedRawEdgePatternReverse (markedRawEdgeStoreOnlyKernel K)) v₀) s ≤ ε := by
    intro s
    rw [hAS,markedRawEdgePatternWeightedAverage_minor_reverse ν _ _ hdisj hZ ψ η d₀ Y Q ρ v₀ χ bs,
      markedRawEdgePatternWeightedAverage_minor_swap ν V (fun j => (hV j).ne') hZ
        (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ v₀ χ (markedRawEdgePatternReverse bs)]
    have hker : (fun p q u v =>
        (markedRawEdgeFlagChargeSwap V p q * markedRawEdgePatternReverse bs p q u v) *
          markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ u v) =
        markedRawEdgePromotedKernel (fun p q u v => βn p q u v *
          markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ u v) := by
      funext p q u v
      by_cases hp : p = fun _ => false <;> by_cases hq : q = fun _ => false <;>
        simp [bs,βn,markedRawEdgePatternReverse,markedRawEdgePromotedKernel,markedRawEdgeFlagGate,hp,hq]
    rw [hker]
    exact hpromR βn hβn s
  have hKL : ∀ p q z a t,MarkedRawMemorySymmetric (fun m => K p q (z,(a,m)) t) := by
    intro p q z a t m σ
    exact markedRawEdgeJointCoefficient_source_permute hZ ψ η d₀ Y Q ρ χ hχ z a m σ t
  have hKR : ∀ p q s z a,MarkedRawMemorySymmetric (fun m => K p q s (z,(a,m))) := by
    intro p q s z a m σ
    exact markedRawEdgeJointCoefficient_target_permute hZ ψ η d₀ Y Q ρ χ hχ s z a m σ
  constructor
  · exact markedRawEdgePatternSymmetrized_energy_le_of_rows ν (fun j => (V j)⁻¹) (fun _ => 1)
      hν (fun j => (inv_pos.mpr (hV j)).le) (fun _ => zero_le_one) hZ (markedRawEdgePromotedKernel K)
      (markedRawEdgeFlagGate_source_symmetric _ K hKL)
      (markedRawEdgeFlagGate_target_symmetric _ K hKR)
      hv₀ hε (add_nonneg hε hC) hpromRow hpromCol f hf
  · exact markedRawEdgePatternSymmetrized_energy_le_of_rows ν (fun j => (V j)⁻¹) (fun _ => 1)
      hν (fun j => (inv_pos.mpr (hV j)).le) (fun _ => zero_le_one) hZ (markedRawEdgeStoreOnlyKernel K)
      (markedRawEdgeFlagGate_source_symmetric _ K hKL)
      (markedRawEdgeFlagGate_target_symmetric _ K hKR)
      hv₀ hC hε hstoreRow hstoreCol f hf

end
end ArtinMatthews
