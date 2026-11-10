module

public import ArtinMatthews.MarkedTypeIIDeterminantCutoff
public import ArtinMatthews.MarkedMajorFixedCharacterInterval
public import ArtinMatthews.MarkedPhysicalCoprimeScalarDetector
public import ArtinMatthews.MarkedTypeIIDyadQuotient
public import ArtinMatthews.MarkedTypeIIDyadDeltaSum
public import ArtinMatthews.MarkedTypeIIScalarMajorJoinActual
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

/-! The actual occupied Cauchy determinant minus the original major is
within the proved shared-label error of the coprime scalar minor. -/
namespace ArtinMatthews
noncomputable section
open Filter Finset

theorem markedTypeII_occupied_determinant_sub_major_error_log_saving
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (ψ : SchwartzMap ℝ ℂ) (R W δ C Qexp K D : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) (hδ : 0 < δ) (hK : 0 < K)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-R) R)
    (hψone : ∀ t ∈ Set.Icc (-4:ℝ) 4,ψ t=1) :
    ∀ᶠ L : ℝ in atTop, ∀ H U Y modulation : ℝ, ∀ (S : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ),
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ K*Real.exp L →
      (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → 0 < Y →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      let Wrough := Real.exp (L^(6/25:ℝ))
      let αχ := fun m => ξ (m:ℕ)*markedMajorCenteredCoefficient Wrough modulation m
      let βχ := fun n => ξ (n:ℕ)*β n
      ‖(markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y S (Icc l r))
          (markedTypeIILabelEndpointCoefficient P Y αχ βχ) -
        markedMajorFixedIntervalPairSum P ξ markedTypeIILabelCutoff ψ (L^Qexp) Y
          Wrough modulation S S l r β) -
        markedPhysicalCoprimeScalarDetectorSum P S (Icc l r) markedTypeIILabelCutoff Y
          (markedBanEdgeKernel ψ (L^Qexp) Y) αχ βχ‖ ≤ (Y*(H*U))*L^(-D) := by
  filter_upwards [markedPhysicalScalar_fixed_delta_sub_major_error_log_saving e he ξ
    markedTypeIILabelCutoff ψ R W δ C Qexp K D hR hW hδ hK
    markedTypeIILabelCutoff_norm_le_one markedTypeIILabelCutoff_support hψ hsupp] with L h
  intro H U Y modulation S l r β hH hU hX hS hl hr hY hβ
  dsimp only
  rw [markedTypeII_occupied_determinant_eq_coprime_delta _ Y ψ S (Icc l r) _ _ hψone]
  exact h H U Y modulation S l r β hH hU hX hS hl hr hY hβ

theorem markedTypeII_actual_determinant_sub_major_error_log_saving
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ) (δ C Qexp K D : ℝ)
    (hδ : 0 < δ) (hK : 0 < K) :
    ∀ᶠ L : ℝ in atTop, ∀ H U Y modulation : ℝ, ∀ (S : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ),
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ K*Real.exp L →
      (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → 0 < Y →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      let Wrough := Real.exp (L^(6/25:ℝ))
      let αχ := fun m => ξ (m:ℕ)*markedMajorCenteredCoefficient Wrough modulation m
      let βχ := fun n => ξ (n:ℕ)*β n
      ‖(markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y S (Icc l r))
          (markedTypeIILabelEndpointCoefficient P Y αχ βχ) -
        markedMajorFixedIntervalPairSum P ξ markedTypeIILabelCutoff markedTypeIIDeterminantCutoff
          (L^Qexp) Y Wrough modulation S S l r β) -
        markedPhysicalCoprimeScalarDetectorSum P S (Icc l r) markedTypeIILabelCutoff Y
          (markedBanEdgeKernel markedTypeIIDeterminantCutoff (L^Qexp) Y) αχ βχ‖ ≤
            (Y*(H*U))*L^(-D) :=
  markedTypeII_occupied_determinant_sub_major_error_log_saving e he ξ
    markedTypeIIDeterminantCutoff 5 1 δ C Qexp K D (by norm_num) (by norm_num) hδ hK
    markedTypeIIDeterminantCutoff_norm_le_one markedTypeIIDeterminantCutoff_support
    markedTypeIIDeterminantCutoff_one

end
end ArtinMatthews
