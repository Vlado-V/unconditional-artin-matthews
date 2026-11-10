module

public import ArtinMatthews.SpectralEisensteinOutgoingModes
public import ArtinMatthews.SpectralCompactChartHeight
public import ArtinMatthews.SpectralCuspSmoothUnfolding
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Every actual compact seed and all its modular translates have a
uniform height bound on their support. The corresponding full ambient
forcing vanishes against every genuine high translated compact test. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

structure Gamma0CompactResolventCutoff (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) where
  height : ℝ
  matching_le : gamma0EisensteinMatchingHeight N≤height
  modular_height_le : ∀ δ : SL(2,ℤ), ∀ z∈tsupport ψ.val,(δ • z).im≤height

theorem Gamma0CompactResolventCutoff.pos {N : ℕ} [NeZero N] {ψ : h2SmoothCompactSeeds}
    (A : Gamma0CompactResolventCutoff N ψ) : 0<A.height :=
  (gamma0EisensteinMatchingHeight_pos N).trans_le A.matching_le

theorem Gamma0CompactResolventCutoff.high {N : ℕ} [NeZero N] {ψ : h2SmoothCompactSeeds}
    (A : Gamma0CompactResolventCutoff N ψ) (r : SL(2,ℤ)) :
    2*(gamma0CuspTrueWidth N r:ℝ)≤A.height :=
  (gamma0EisensteinMatchingHeight_high N r).trans A.matching_le

def gamma0CompactResolventCutoff (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    Gamma0CompactResolventCutoff N ψ :=
  let h := compact_modular_images_height_bound ψ.val.hasCompactSupport
  ⟨max (gamma0EisensteinMatchingHeight N) (Classical.choose h),le_max_left _ _,
    fun δ z hz => ((Classical.choose_spec h).2 δ z hz).trans (le_max_right _ _)⟩

theorem Gamma0CompactResolventCutoff.cuspSection_zero {N : ℕ} [NeZero N]
    {ψ : h2SmoothCompactSeeds} (A : Gamma0CompactResolventCutoff N ψ)
    (r : SL(2,ℤ)) (z : UpperHalfPlane) (hz : A.height<z.im) :
    gamma0CuspSection N ψ r z=0 := by
  by_contra hn
  obtain ⟨γ,hγ⟩ := gamma0PoincareSeed_support N ψ.val hn
  have hb := A.modular_height_le (r*(γ:SL(2,ℤ))⁻¹) _ hγ
  rw [mul_smul,inv_smul_smul,smul_inv_smul] at hb
  exact (not_le_of_gt hz) hb

theorem Gamma0CompactResolventCutoff.mass_tail_test_zero {N : ℕ} [NeZero N]
    {ψ : h2SmoothCompactSeeds} (A : Gamma0CompactResolventCutoff N ψ)
    (r : SL(2,ℤ)) (φ : h2SmoothCompactSeeds)
    (hφ : ∀ z∈Function.support (fun z : UpperHalfPlane => φ.val z),A.height<z.im) :
    inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r φ))
      (gamma0SmoothSeedMass N ψ)=0 := by
  rw [gamma0SmoothSeedMass_inner_unfold_translated]
  have h : (∫ z : UpperHalfPlane, inner ℂ (φ.val z) (gamma0CuspSection N ψ r z))=0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun z => by
      change inner ℂ (φ.val z) (gamma0CuspSection N ψ r z)=0
      by_cases hz : φ.val z=0
      · rw [hz,inner_zero_left]
      · rw [A.cuspSection_zero r z (hφ z hz),inner_zero_right]
  rw [h,mul_zero]

end ArtinMatthews
