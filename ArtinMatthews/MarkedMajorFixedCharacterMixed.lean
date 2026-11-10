module

public import ArtinMatthews.MarkedMajorFixedCharacterInterval
public import ArtinMatthews.MarkedMajorTypeIIBands
public import ArtinMatthews.MarkedMajorTypeIIData
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Actual fixed-character PD03 band and coefficient data on two independently chosen
intervals, including the comparable scale needed for boundary singletons. -/
namespace ArtinMatthews
open Filter Finset ComplexConjugate
open scoped ContDiff

 theorem markedMajor_typeII_fixed_option_mixed {J : Type} [Fintype J] [DecidableEq J]
    (e : Option J → ℝ) (hinj : Function.Injective e)
    (he : ∀ i,(1/10:ℝ)<e i ∧ e i<(1/5:ℝ))
    {Mχ : ℕ} [NeZero Mχ] (ξ : DirichletCharacter ℂ Mχ)
    (δ C A Kx P : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y,‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo/2 < 8*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ L : ℝ in atTop, ∀ H H' U u v u' v' Y modulation : ℝ, ∀ l r : ℕ, ∀ β : ℕ → ℂ,
      Real.exp ((δ/2)*L) ≤ H → Real.exp ((δ/2)*L) ≤ H' → Real.exp ((δ/2)*L) ≤ U →
      H*U ≤ Kx*Real.exp L → H'*U ≤ Kx*Real.exp L → H ≤ 2*H' → H' ≤ 2*H →
      H ≤ u → u ≤ v → v ≤ 2*H → H' ≤ u' → u' ≤ v' → v' ≤ 2*H' →
      U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → 0 < Y → |modulation| ≤ L^C →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      (∀ n ∈ Icc l r,β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖markedMajorFixedIntervalPairSum (fun i => markedLogPowerBand (e i) (Real.exp L)) ξ
        cutoff ψ (L^A) Y (Real.exp (L^(6/25:ℝ))) modulation
        (Ioc ⌊u⌋₊ ⌊v⌋₊) (Ioc ⌊u'⌋₊ ⌊v'⌋₊) l r β‖ ≤ (Y*(H*U))*L^(-P) := by
  let cfg := markedMajorTypeIIConfig δ C A hδ hC hA
  filter_upwards [markedMajor_fixed_comparableMajorSource_all_log cfg 2 Kx (by norm_num) ξ (star ξ)
    cutoff hcutoff hnorm hlo hhi hinterval hsupp ψ hψ P hP,
    markedMajorTypeII_band_data e hinj he A,markedMajorTypeII_scale_budget (δ/2) Kx (half_pos hδ),
    eventually_ge_atTop (1:ℝ)] with L hs hb hrange hL
  intro H H' U u v u' v' Y modulation l r β hH hH' hU hX hX' hHH' hH'H
    hHu huv hvH hH'u' hu'v' hv'H' hl hr hY hmod hβ hrough
  have hUp : 0 < U := (Real.exp_pos _).trans_le hU
  have hscale := hrange H U v hH hU hX hvH
  have hscale' := hrange H' U v' hH' hU hX' hv'H'
  let z := markedMajorTypeIIData δ C A hδ hC hA e L H U u v Y modulation l r β hL
    hb.1 hb.2.1 hb.2.2.1 hY hH hU hHu huv hvH hscale.2.2.1 hl hr hβ hmod
  let z' := markedMajorTypeIIData δ C A hδ hC hA e L H' U u' v' Y modulation l r β hL
    hb.1 hb.2.1 hb.2.2.1 hY hH' hU hH'u' hu'v' hv'H' hscale'.2.2.1 hl hr hβ hmod
  have heq : z.allBands=(fun i => markedLogPowerBand (e i) (Real.exp L)) :=
    markedMajorTypeIIData_allBands ..
  have heq' : z'.allBands=z.allBands := by
    rw [heq]
    exact markedMajorTypeIIData_allBands ..
  have hband : ∀ i p,p ∈ z.allBands i → L^A < (p:ℝ) := by
    simpa only [heq] using hb.2.2.2
  have hband' : ∀ i p,p ∈ z'.conjugateBeta.allBands i → L^A < (p:ℝ) := by
    change ∀ i p,p ∈ z'.allBands i → L^A < (p:ℝ)
    rwa [heq']
  have hrough' : ∀ n ∈ Icc z'.conjugateBeta.l z'.conjugateBeta.r,
      z'.conjugateBeta.β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n := by
    intro n hn hne
    change conj (β n) ≠ 0 at hne
    exact hrough n hn (by simpa only [map_ne_zero] using hne)
  have hsave := hs (H*U) (H'*U) hscale.1 hscale'.1 hscale.2.1 hX hscale'.2.1 hX'
    (by nlinarith) (by nlinarith) z z'.conjugateBeta rfl (L^A)
    (Real.rpow_nonneg (zero_le_one.trans hL) _) le_rfl le_rfl hband hband' hrough hrough'
  rw [markedMajor_fixed_comparable_interval_source_eq z z' heq' rfl rfl rfl rfl ξ] at hsave
  change ‖markedMajorFixedIntervalPairSum z.allBands ξ cutoff ψ (L^A) Y
    (Real.exp (L^(6/25:ℝ))) modulation (Ioc ⌊u⌋₊ ⌊v⌋₊) (Ioc ⌊u'⌋₊ ⌊v'⌋₊) l r β‖ ≤ _ at hsave
  rwa [heq] at hsave

end ArtinMatthews
