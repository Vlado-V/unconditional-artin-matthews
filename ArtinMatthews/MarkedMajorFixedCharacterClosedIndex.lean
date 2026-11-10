module

public import ArtinMatthews.MarkedMajorFixedCharacterInterval
public import ArtinMatthews.MarkedMajorBandReindex
public import ArtinMatthews.MarkedMajorFixedCharacterClosed
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

/-! Full fixed-character closed-interval major saving in the original arbitrary band index
and original x/log(x) variables. -/
namespace ArtinMatthews
open Filter Finset
open scoped ContDiff

 theorem markedMajorFixedIntervalPairSum_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (P : J → Finset ℕ) {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation : ℝ) (S T : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ) :
    markedMajorFixedIntervalPairSum (fun i => P (e i)) ξ cutoff ψ Q Y W modulation S T l r β =
      markedMajorFixedIntervalPairSum P ξ cutoff ψ Q Y W modulation S T l r β := by
  simp only [markedMajorFixedIntervalPairSum,markedMajorLabelSet_reindex,markedMajorLabelMass_reindex]

 theorem markedMajor_typeII_fixed_actual_Icc {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (e : I → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ))
    {Mχ : ℕ} [NeZero Mχ] (ξ : DirichletCharacter ℂ Mχ)
    (δ C A Kx P : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y,‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo/2 < 8*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ L : ℝ in atTop, ∀ H U Y modulation : ℝ, ∀ M N l r : ℕ, ∀ β : ℕ → ℂ,
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ Kx*Real.exp L →
      H ≤ (M:ℝ) → M ≤ N → (N:ℝ) ≤ 2*H → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      0 < Y → |modulation| ≤ L^C → (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      (∀ n ∈ Icc l r,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖markedMajorFixedIntervalPairSum (fun i => markedLogPowerBand (e i) (Real.exp L)) ξ
        cutoff ψ (L^A) Y (Real.exp (L^(6/25:ℝ))) modulation
        (Icc M N) (Icc M N) l r β‖ ≤ (Y*(H*U))*L^(-P) := by
  let E := Equiv.optionSubtypeNe i₀
  have hs := markedMajor_typeII_fixed_option_closed (fun j => e (E j)) (hinj.comp E.injective)
    (fun j => he (E j)) ξ δ C A Kx P hδ hC hA hP cutoff hcutoff hnorm hlo hhi hinterval hsupp ψ hψ
  filter_upwards [hs] with L hL
  intro H U Y modulation M N l r β hH hU hX hHM hMN hNH hl hr hY hmod hβ hrough
  have hb := hL H U Y modulation M N l r β hH hU hX hHM hMN hNH hl hr hY hmod hβ hrough
  rw [markedMajorFixedIntervalPairSum_reindex E (fun i => markedLogPowerBand (e i) (Real.exp L)) ξ] at hb
  exact hb

 theorem markedMajor_typeII_fixed_actual_Icc_log {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (e : I → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ))
    {Mχ : ℕ} [NeZero Mχ] (ξ : DirichletCharacter ℂ Mχ)
    (δ C A Kx P : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y,‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo/2 < 8*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ x : ℝ in atTop, ∀ H U Y modulation : ℝ, ∀ M N l r : ℕ, ∀ β : ℕ → ℂ,
      x^δ ≤ H → x^δ ≤ U → H*U ≤ Kx*x →
      H ≤ (M:ℝ) → M ≤ N → (N:ℝ) ≤ 2*H → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      0 < Y → |modulation| ≤ (Real.log x)^C → (∀ n ∈ Icc l r,‖β n‖ ≤ (Real.log x)^C) →
      (∀ n ∈ Icc l r,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp ((Real.log x)^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖markedMajorFixedIntervalPairSum (fun i => markedLogPowerBand (e i) x) ξ
        cutoff ψ ((Real.log x)^A) Y (Real.exp ((Real.log x)^(6/25:ℝ))) modulation
        (Icc M N) (Icc M N) l r β‖ ≤ (Y*(H*U))*(Real.log x)^(-P) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (markedMajor_typeII_fixed_actual_Icc i₀ e hinj he ξ δ C A Kx P hδ hC hA hP
      cutoff hcutoff hnorm hlo hhi hinterval hsupp ψ hψ),eventually_gt_atTop (0:ℝ)] with x hx hxpos
  have heq : Real.exp (δ*Real.log x)=x^δ := by
    rw [Real.rpow_def_of_pos hxpos,mul_comm]
  simpa only [Real.exp_log hxpos,heq] using hx

end ArtinMatthews
