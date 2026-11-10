module

public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeRow
public import ArtinMatthews.MarkedMinorArcRawGhostWeight
public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceMass
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgePromotionBound
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeWeight
public import ArtinMatthews.MarkedMinorArcRawEdgeCrudeFiber
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

/-! With no promoted old index there is no B-dependent choice count.
All stores and all fresh labels remain in this literal row. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawEdgeCrude_empty_row_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) {N : ℝ} (hN : 1 ≤ N) (hνN : ∀ j,(∑ p,ν j p) ≤ N)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ H W A : ℝ)
    (hY : 0 < Y) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W)
    (hsupp : ∀ t,ψ t ≠ 0 → |t| ≤ A)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s,‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (w : ℤ × ℤ) (hw : markedMinorIntegerDet s.1.1 w=1)
    (hτ : markedMinorIntegerTau r s.1.1 ≠ 0)
    (hbox : ∀ v ∈ Z,|markedMinorIntegerTau r v/markedMinorIntegerTau r s.1.1| ≤ 16) :
    markedRawEdgeCrudeFixedAbsRow ν V hZ ψ η d₀ Y Q ρ χ s ∅ ≤
      (2*N)^(Fintype.card J)*H^2*(33*W*(1+(2*A*Y+1)*(4*Q^3/Y))) := by
  classical
  let E := H^2*(33*W*(1+(2*A*Y+1)*(4*Q^3/Y)))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let μ := finiteProductMass (fun j : ↥(Finset.univ \ (∅ : Finset J)) => ν j.1)
  have hμ (fresh) : 0 ≤ μ fresh := Finset.prod_nonneg (fun j _ => hν _ _)
  have hpoint (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 ∅)
      (fresh : (j : ↥(Finset.univ \ (∅ : Finset J))) → ↥(P j.1)) :
      (∑ c ∈ markedDirtyMajorChoiceFiber hZ s ∅ store indices fresh,
        markedRawEdgeChoicePrimeMass ν V hZ s c.1*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c.1‖) ≤
      μ fresh*E := by
    calc
      _ = μ fresh*∑ c ∈ markedDirtyMajorChoiceFiber hZ s ∅ store indices fresh,
          ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c.1‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        rw [markedDirtyMajorChoiceFiber_prime_mass ν V hZ s ∅ store indices fresh c hc]
        simp only [Finset.prod_empty,mul_one]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (markedRawEdgeCrude_fiber_sum_le hZ ψ η r d₀ Y Q ρ H W A hY hQ hA hρ₀ hρ₁ hH hW
          hη hψ hsupp χ hχ s w hw hτ hbox ∅ store indices fresh) (hμ fresh)
  have hm := markedRawEdgeCrude_fresh_mass_le ν hν hN hνN ∅
  unfold markedRawEdgeCrudeFixedAbsRow
  rw [markedDirtyMajorChoice_fiberwise_sum]
  calc
    _ ≤ ∑ _store : J → Bool,∑ _indices : MarkedRawPromotionTuple s.2.2 ∅,
        ∑ fresh : (j : ↥(Finset.univ \ (∅ : Finset J))) → ↥(P j.1),μ fresh*E :=
      Finset.sum_le_sum (fun store _ => Finset.sum_le_sum (fun indices _ =>
        Finset.sum_le_sum (fun fresh _ => hpoint store indices fresh)))
    _ = (2:ℝ)^(Fintype.card J)*(∑ fresh,μ fresh)*E := by simp [Finset.sum_mul,mul_assoc]
    _ ≤ (2:ℝ)^(Fintype.card J)*N^(Fintype.card J)*E := by gcongr
    _ = _ := by dsimp [E]; rw [mul_pow]; ring

def markedRawEdgeNoPromotionWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) : ℝ :=
  ∑ c : MarkedDirtyFixedEdgeChoice hZ s ∅,
    markedRawEdgeChoicePrimeMass ν V hZ s c.1*‖modifier c.1*markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c.1‖*
      (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c.1)/markedRawMemorySchurWeight v₀ s.2.2)

theorem markedRawEdgeNoPromotionWeightedRow_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ) (hv₀ : 1 ≤ v₀)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (modifier : MarkedRawEdgeChoice hZ s → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hmodifier : ∀ c,‖modifier c‖ ≤ L) :
    markedRawEdgeNoPromotionWeightedRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s modifier ≤
      (L*v₀^(Fintype.card J))*markedRawEdgeCrudeFixedAbsRow ν V hZ ψ η d₀ Y Q ρ χ s ∅ := by
  classical
  unfold markedRawEdgeNoPromotionWeightedRow markedRawEdgeCrudeFixedAbsRow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hm := markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s c.1
  have hvpos : 0 < v₀ := zero_lt_one.trans_le hv₀
  have hw : 0 ≤ markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c.1)/
      markedRawMemorySchurWeight v₀ s.2.2 :=
    div_nonneg (markedRawMemorySchurWeight_pos hvpos _).le (markedRawMemorySchurWeight_pos hvpos _).le
  have hn : ‖modifier c.1*markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c.1‖ ≤
      L*‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c.1‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hmodifier c.1) (norm_nonneg _)
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hn hm)
    (markedDirtyRawEdge_target_weight_ratio_le hZ s c.1 hv₀) hw
    (mul_nonneg hm (mul_nonneg hL (norm_nonneg _)))).trans_eq (by ring)

end
end ArtinMatthews
