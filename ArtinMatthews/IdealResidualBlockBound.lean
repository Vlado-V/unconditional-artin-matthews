module

public import ArtinMatthews.IdealFirstCoordinates
public import ArtinMatthews.IdealLabelPairing
public import ArtinMatthews.IdealSelectedComparisonTransport
public import ArtinMatthews.IdealResidualExceptionalBound
public import ArtinMatthews.IdealResidualFamilyError
public import ArtinMatthews.IdealSymmetricProbe
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The original symmetric residual family contracts by the two actual
full-probe survivor factors and its full comparison-error budget. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealResidualOperator_block_pairing {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell m : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p) (S T : Finset (G × Fin k)) (hST : Disjoint S T)
    (probeSlots tailSlots : G → Finset (Fin (k+ell))) (G₁ G₂ : Finset G)
    (hp₁ : ∀ j∈G₁,∀ i∈probeSlots j,(j,i)∈idealFirstCoordinates ell S)
    (hp₂ : ∀ j∈G₂,∀ i∈probeSlots j,(j,i)∈idealFirstCoordinates ell T)
    (ht : ∀ j i,i∈tailSlots j → (j,i)∈idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k))))
    (hdis : ∀ j,Disjoint (probeSlots j) (tailSlots j)) (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hpCard : ∀ j,(probeSlots j).card=m) (htCard : ∀ j,(tailSlots j).card=ell)
    (hlarge : (m+ell)*(m+ell-1) ≤ k+ell)
    (Q : ℕ) (h ξ Θ ζ : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcmp : ∀ A∈S.powerset.erase ∅,∀ B∈T.powerset.erase ∅,∀ α u v,
      ‖idealSelectedComparisonForm (idealResidualBands P A) (idealResidualBands P B) Q h ξ ζ α u v‖ ≤
      ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P A)) u)*
        Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P B)) v))
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) (hf : IdealSymmetric f) (hg : IdealSymmetric g) :
    ‖idealLabelPairing P f (idealResidualOperator P S T Q h ξ Θ ζ g)‖ ≤
      (Real.sqrt (((2:ℝ)/(m+1:ℕ))^G₁.card)+Real.sqrt (((2:ℝ)/(m+1:ℕ))^G₂.card)+
        (2:ℝ)^(S.card+T.card)*ε)*idealLabelNorm P f*idealLabelNorm P g := by
  have hM : 0 < k+ell := by omega
  have h₁ := idealProbeProjection_uniform_bound P hV hP (idealFirstCoordinates ell S)
    (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) probeSlots tailSlots G₁
    hp₁ (fun j _ i hi => ht j i hi) (fun j _ => hdis j) hM hm hell
    (fun j _ => hpCard j) (fun j _ => htCard j) hlarge f hf
  have h₂ := idealProbeProjection_uniform_bound P hV hP (idealFirstCoordinates ell T)
    (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) probeSlots tailSlots G₂
    hp₂ (fun j _ i hi => ht j i hi) (fun j _ => hdis j) hM hm hell
    (fun j _ => hpCard j) (fun j _ => htCard j) hlarge g hg
  have hp₁nonneg : 0 ≤ ((2:ℝ)/(m+1:ℕ))^G₁.card := by positivity
  have hp₂nonneg : 0 ≤ ((2:ℝ)/(m+1:ℕ))^G₂.card := by positivity
  have hn₁ : idealLabelNorm P (idealProbeProjection P (idealFirstCoordinates ell S)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f) ≤
      Real.sqrt (((2:ℝ)/(m+1:ℕ))^G₁.card)*idealLabelNorm P f := by
    apply idealLabelNorm_energy_bound P hV _ f (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hp₁nonneg]
    exact h₁
  have hn₂ : idealLabelNorm P (idealProbeProjection P (idealFirstCoordinates ell T)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g) ≤
      Real.sqrt (((2:ℝ)/(m+1:ℕ))^G₂.card)*idealLabelNorm P g := by
    apply idealLabelNorm_energy_bound P hV _ g (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hp₂nonneg]
    exact h₂
  have he := idealResidual_exception_norm P hV hP S T Θ ζ f g
  have herr := idealResidualFamily_pairing_bound P hV hP S T hST Q h ξ Θ ζ hε hcmp f g hf hg
  calc
    _ ≤ ‖idealResidualExceptionalPairing P S T Θ ζ f g‖+
        (2:ℝ)^(S.card+T.card)*ε*idealLabelNorm P f*idealLabelNorm P g := herr
    _ ≤ (idealLabelNorm P (idealProbeProjection P (idealFirstCoordinates ell S)
          (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f)*idealLabelNorm P g+
        idealLabelNorm P f*idealLabelNorm P (idealProbeProjection P (idealFirstCoordinates ell T)
          (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) g))+
        (2:ℝ)^(S.card+T.card)*ε*idealLabelNorm P f*idealLabelNorm P g := add_le_add he le_rfl
    _ ≤ (Real.sqrt (((2:ℝ)/(m+1:ℕ))^G₁.card)*idealLabelNorm P f*idealLabelNorm P g+
        idealLabelNorm P f*(Real.sqrt (((2:ℝ)/(m+1:ℕ))^G₂.card)*idealLabelNorm P g))+
        (2:ℝ)^(S.card+T.card)*ε*idealLabelNorm P f*idealLabelNorm P g := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hn₁ (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_left hn₂ (Real.sqrt_nonneg _))) le_rfl
    _ = _ := by ring

end
end ArtinMatthews
