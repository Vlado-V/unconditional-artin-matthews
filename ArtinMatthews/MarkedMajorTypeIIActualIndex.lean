module

public import ArtinMatthews.MarkedMajorArcPaperSource
public import ArtinMatthews.MarkedMajorBandReindex
public import ArtinMatthews.MarkedMajorTypeIIActual
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

/-! Arbitrary nonempty indexing of the actual bands, with exact reindexing
of labels and all reciprocal-mass normalizers. -/
namespace ArtinMatthews
open Filter Finset
open scoped ContDiff

 theorem markedMajor_typeII_actual_Ioc {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (e : I → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ))
    (δ C A Kx P : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y,‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo < 4*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ L : ℝ in atTop, ∀ H U u v Y modulation : ℝ, ∀ l r : ℕ, ∀ β : ℕ → ℂ,
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ Kx*Real.exp L →
      H ≤ u → u ≤ v → v ≤ 2*H → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      0 < Y → |modulation| ≤ L^C → (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      (∀ n ∈ Icc l r,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖markedMajorDeterminantPaperSum (fun i => markedLogPowerBand (e i) (Real.exp L))
        cutoff ψ (L^A) Y (Real.exp (L^(6/25:ℝ))) modulation u v l r β‖ ≤ (Y*(H*U))*L^(-P) := by
  let E := Equiv.optionSubtypeNe i₀
  have hs := markedMajor_typeII_option_actual (fun j => e (E j)) (hinj.comp E.injective)
    (fun j => he (E j)) δ C A Kx P hδ hC hA hP cutoff hcutoff hnorm hlo hhi hinterval hsupp ψ hψ
  filter_upwards [hs] with L hL
  intro H U u v Y modulation l r β hH hU hX hHu huv hvH hl hr hY hmod hβ hrough
  have hb := hL H U u v Y modulation l r β hH hU hX hHu huv hvH hl hr hY hmod hβ hrough
  rw [markedMajorDeterminantPaperSum_reindex E (fun i => markedLogPowerBand (e i) (Real.exp L))] at hb
  exact hb

 theorem markedMajor_typeII_actual_Ioc_log {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (e : I → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ))
    (δ C A Kx P : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y,‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo < 4*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ x : ℝ in atTop, ∀ H U u v Y modulation : ℝ, ∀ l r : ℕ, ∀ β : ℕ → ℂ,
      x^δ ≤ H → x^δ ≤ U → H*U ≤ Kx*x →
      H ≤ u → u ≤ v → v ≤ 2*H → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      0 < Y → |modulation| ≤ (Real.log x)^C → (∀ n ∈ Icc l r,‖β n‖ ≤ (Real.log x)^C) →
      (∀ n ∈ Icc l r,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp ((Real.log x)^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖markedMajorDeterminantPaperSum (fun i => markedLogPowerBand (e i) x)
        cutoff ψ ((Real.log x)^A) Y (Real.exp ((Real.log x)^(6/25:ℝ))) modulation u v l r β‖ ≤
          (Y*(H*U))*(Real.log x)^(-P) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (markedMajor_typeII_actual_Ioc i₀ e hinj he δ C A Kx P hδ hC hA hP
      cutoff hcutoff hnorm hlo hhi hinterval hsupp ψ hψ),eventually_gt_atTop (0:ℝ)] with x hx hxpos
  have heq : Real.exp (δ*Real.log x)=x^δ := by
    rw [Real.rpow_def_of_pos hxpos,mul_comm]
  simpa only [Real.exp_log hxpos,heq] using hx

end ArtinMatthews
