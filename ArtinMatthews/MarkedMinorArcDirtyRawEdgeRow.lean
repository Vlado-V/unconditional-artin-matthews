module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeCodeAverage
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeTargetMap
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeCoreDomination
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

/-! Literal source-symmetrized delta edge rows, including all stores and
all admissible indexed promotion/fresh choices, are bounded by the proved
counted expectation. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyRawEdgeDeltaRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ η : ℝ → ℂ) (d₀ Y ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) : ℝ := by
  classical
  exact ∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ *
    ∑ choice : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I,
      markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) choice.1 *
        ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
          (markedRawSlotEquiv σ s) choice.1‖

set_option backward.isDefEq.respectTransparency false in
theorem markedDirtyRawEdge_delta_row_le_counted_expectation {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {C : ℝ} (hC : 1 ≤ C) (hVC : ∀ j, (V j)⁻¹ ≤ C)
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ η : ℝ → ℂ) (d₀ Y : ℝ)
    {ρ H W : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) (jstar : J) (hstar : jstar ∈ I)
    (Q : Finset ℤ) (hQ : markedDirtyRawEdgeTrials s.2.1 s.2.2 (I.erase jstar) ⊆ Q) :
    markedDirtyRawEdgeDeltaRow ν V hZ ψ η d₀ Y ρ χ s I ≤
      (C^(Fintype.card J)*H^2*W*(2:ℝ)^(Fintype.card J))*
        ∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
          finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh *
            markedRawDirtyGoodChoiceMass s.2.1 s.2.2 jstar (I.erase jstar) Z hZ s.1.1
              (markedDirtyRawFreshIntegerProduct fresh) Q ρ (fun _ _ _ => 0) := by
  classical
  let D : ℝ := C^(Fintype.card J)*H^2*W
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hg (o : J → Fin (pads+1)) (code : MarkedDirtyIndependentCode s.2.2 I Z) :
      0 ≤ markedDirtyRawDeltaCodeMass s.2.1 s.2.2 I jstar hstar ν Z hZ s.1.1 Q ρ o code := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun j _ => hν _ _)
    · exact markedDirtyRawCoreGate_nonneg _ _ _ _ _ _ _ _ _ hρ₀ _ _ _ _
  have hrow (σ : J → Equiv.Perm (Fin (pads+1))) :
      (∑ choice : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I,
        markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) choice.1 *
          ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
            (markedRawSlotEquiv σ s) choice.1‖) ≤
      D*∑ code : MarkedDirtyIndependentCode s.2.2 I Z,
        markedDirtyRawDeltaCodeMass s.2.1 s.2.2 I jstar hstar ν Z hZ s.1.1 Q ρ
          (fun j => σ j (Fin.last pads)) code := by
    let e : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I → MarkedDirtyIndependentCode s.2.2 I Z :=
      markedDirtyFixedEdgeChoiceCode hZ (markedRawSlotEquiv σ s) I
    have he : Function.Injective e := markedDirtyFixedEdgeChoiceCode_injective hZ (markedRawSlotEquiv σ s) I
    calc
      _ ≤ ∑ code : MarkedDirtyIndependentCode s.2.2 I Z,
          D*markedDirtyRawDeltaCodeMass s.2.1 s.2.2 I jstar hstar ν Z hZ s.1.1 Q ρ
            (fun j => σ j (Fin.last pads)) code := by
        apply markedDirtyFinite_sum_le_of_injective e he _ _
          (fun code => mul_nonneg hD (hg _ code))
        intro choice
        simpa only [D,markedDirtyRawDeltaCodeMass,mul_assoc] using
          markedDirtyRawEdge_delta_choice_core_le ν V hν hV hC hVC hZ ψ η d₀ Y hρ₀ hρ₁ hH hW hη hψ χ hχ
            s I jstar hstar Q hQ σ choice
      _ = _ := (Finset.mul_sum _ _ _).symm
  unfold markedDirtyRawEdgeDeltaRow
  calc
    _ ≤ ∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ*
        (D*∑ code : MarkedDirtyIndependentCode s.2.2 I Z,
          markedDirtyRawDeltaCodeMass s.2.1 s.2.2 I jstar hstar ν Z hZ s.1.1 Q ρ
            (fun j => σ j (Fin.last pads)) code) :=
      Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hrow σ) (by
        unfold markedDirtySourceSlotWeight
        positivity))
    _ = D*∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ*
        ∑ code : MarkedDirtyIndependentCode s.2.2 I Z,
          markedDirtyRawDeltaCodeMass s.2.1 s.2.2 I jstar hstar ν Z hZ s.1.1 Q ρ
            (fun j => σ j (Fin.last pads)) code := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (markedDirtyRawDeltaCodeMass_average_le s.2.1 s.2.2 I jstar hstar ν hν Z hZ s.1.1 Q hρ₀) hD).trans_eq
        (by dsimp [D]; ring)

end ArtinMatthews
