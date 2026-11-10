module

public import ArtinMatthews.SpectralEisensteinProfileGradient
public import ArtinMatthews.SpectralEisensteinCompactProfile
public import ArtinMatthews.SpectralEisensteinProfileLocalFinite
public import ArtinMatthews.SpectralModularGradientChart
public import ArtinMatthews.SpectralPoincareUnfoldingGradientSupport
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

/-! Differentiation of the actual locally finite height-profile sum. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0CuspHeightProfile_local_sum_zero (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (f : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (hlow : ∀ t ≤ ε, f t=0)
    (z : UpperHalfPlane) :
    ∃ T : Finset (Gamma0CuspEisensteinRows N 1 a),
      (gamma0CuspHeightProfile N a f =ᶠ[𝓝 z]
        fun w => (1/2:ℂ)*∑ v ∈ T, cuspEisensteinProfileTerm N 1 a f v w) ∧
      ∀ v ∉ T, cuspEisensteinProfileTerm N 1 a f v =ᶠ[𝓝 z] fun _ => 0 := by
  classical
  obtain ⟨K,hK,hfin⟩ := cuspEisensteinProfile_locallyFinite N 1 a f hε hlow z
  refine ⟨hfin.toFinset,?_,?_⟩
  · filter_upwards [hK] with w hw
    unfold gamma0CuspHeightProfile
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro v hv
    exact hfin.mem_toFinset.mpr ⟨w,hv,hw⟩
  · intro v hv
    filter_upwards [hK] with w hw
    by_contra hn
    exact hv (hfin.mem_toFinset.mpr ⟨w,hn,hw⟩)

theorem gamma0CuspHeightProfile_gradient_hasFiniteSupport (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (f : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (hlow : ∀ t ≤ ε, f t=0)
    (z : UpperHalfPlane) :
    Function.HasFiniteSupport (fun v : Gamma0CuspEisensteinRows N 1 a =>
      h2SectionGradient (cuspEisensteinProfileTerm N 1 a f v) z) := by
  classical
  obtain ⟨T,_,hzero⟩ := gamma0CuspHeightProfile_local_sum_zero N a f hε hlow z
  apply T.finite_toSet.subset
  intro v hv
  by_contra hn
  have he := h2SectionGradient_congr_of_eventuallyEq _ _ z (hzero v hn)
  rw [h2SectionGradient_zero] at he
  exact hv he

theorem gamma0CuspHeightProfile_gradient_tsum (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    {ε : ℝ} (hε : 0 < ε) (hlow : ∀ t ≤ ε, f t=0) (z : UpperHalfPlane) :
    h2SectionGradient (gamma0CuspHeightProfile N a f) z=
      (1/2:ℂ) • ∑' v : Gamma0CuspEisensteinRows N 1 a,
        h2SectionGradient (cuspEisensteinProfileTerm N 1 a f v) z := by
  classical
  obtain ⟨T,he,hzero⟩ := gamma0CuspHeightProfile_local_sum_zero N a f hε hlow z
  have hs : ContDiffOn ℝ ∞
      (fun w : ℂ => ∑ v ∈ T, cuspEisensteinProfileTerm N 1 a f v (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im} :=
    ContDiffOn.sum (fun v _ => cuspEisensteinProfileTerm_smooth N 1 a f hf v)
  rw [h2SectionGradient_congr_of_eventuallyEq _ _ z he]
  change h2SectionGradient ((1/2:ℂ) •
      (fun w => ∑ v ∈ T, cuspEisensteinProfileTerm N 1 a f v w)) z=_
  rw [h2SectionGradient_smul _ _ hs,h2SectionGradient_finset_sum T _
    (fun v => cuspEisensteinProfileTerm_smooth N 1 a f hf v)]
  congr 1
  symm
  apply tsum_eq_sum
  intro v hv
  rw [h2SectionGradient_congr_of_eventuallyEq _ _ z (hzero v hv),h2SectionGradient_zero]

end ArtinMatthews
