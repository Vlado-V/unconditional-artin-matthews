module

public import ArtinMatthews.SpectralEisensteinCriticalTests
public import ArtinMatthews.SpectralEisensteinCriticalPoleRemoval
public import ArtinMatthews.SpectralEisensteinReflectionFamily
public import ArtinMatthews.SpectralEisensteinReflectionScattering
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

/-! The genuine reflected Eisenstein equation transports positive
critical pole removal to the entire critical line. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspEisensteinCanonicalTest_eventually_eq (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ψ : h2SmoothCompactSeeds) (s : ℂ) :
    gamma0CuspEisensteinCanonicalTest N a ψ =ᶠ[𝓝[≠] s] gamma0CuspEisensteinMeromorphicTest N a ψ := by
  filter_upwards [(gamma0CuspEisensteinMeromorphicTest_meromorphic N a ψ s).eventually_analyticAt] with w hw
  exact gamma0CuspEisensteinCanonicalTest_eq_of_analytic N a ψ w hw

theorem gamma0CuspEisensteinMeromorphicTest_reflection_canonical_germ (N : ℕ) [NeZero N]
    (j : Gamma0EisensteinCuspClasses N) (ψ : h2SmoothCompactSeeds) (s : ℂ) :
    gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N j) ψ
      =ᶠ[𝓝[≠] s] fun w => ∑ k,gamma0CuspScatteringCanonical N w k j*
        gamma0CuspEisensteinCanonicalTest N (gamma0EisensteinCuspClassRepresentative N k) ψ (1-w) := by
  have he := (eisensteinParameterReflect_tendsto_punctured s).eventually
    (gamma0CuspEisensteinMeromorphicTest_reflection_germ N j ψ (1-s))
  have hAll : ∀ᶠ w in 𝓝[≠] s,∀ k : Gamma0EisensteinCuspClasses N,
      gamma0CuspEisensteinCanonicalTest N (gamma0EisensteinCuspClassRepresentative N k) ψ (1-w)=
        gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N k) ψ (1-w) := by
    apply eventually_all.mpr
    intro k
    exact (eisensteinParameterReflect_tendsto_punctured s).eventually
      (gamma0CuspEisensteinCanonicalTest_eventually_eq N (gamma0EisensteinCuspClassRepresentative N k) ψ (1-s))
  filter_upwards [he,hAll] with w hw hkw
  rw [show (1:ℂ)-(1-w)=w by ring] at hw
  simpa only [hkw] using hw

theorem gamma0CuspEisensteinMeromorphicTest_order_all_critical (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (j : Gamma0EisensteinCuspClasses N) (t : ℝ) :
    0 ≤ meromorphicOrderAt
      (gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N j) ψ)
      (eisensteinCriticalPoint t) := by
  rcases le_or_gt 0 t with ht | ht
  · exact gamma0CuspEisensteinMeromorphicTest_order_critical N ψ j t ht
  · let s := eisensteinCriticalPoint t
    have hq : 1-s=eisensteinCriticalPoint (-t) := by
      simp only [s,eisensteinCriticalPoint,Complex.ofReal_neg]
      push_cast
      ring
    let H (w : ℂ) := ∑ k,gamma0CuspScatteringCanonical N w k j*
      gamma0CuspEisensteinCanonicalTest N (gamma0EisensteinCuspClassRepresentative N k) ψ (1-w)
    have hH : AnalyticAt ℂ H s := by
      apply Finset.analyticAt_fun_sum
      intro k _
      apply (gamma0CuspScatteringCanonical_entry_analyticAt_critical N t k j).mul
      have h := gamma0CuspEisensteinCanonicalTest_analyticAt_critical N ψ k (-t) (neg_nonneg.mpr ht.le)
      rw [← hq] at h
      exact h.comp (f:=fun w : ℂ => 1-w) (analyticAt_const.sub analyticAt_id)
    rw [meromorphicOrderAt_congr (gamma0CuspEisensteinMeromorphicTest_reflection_canonical_germ N j ψ s)]
    exact hH.meromorphicOrderAt_nonneg

theorem gamma0CuspEisensteinCanonicalTest_analyticAt_all_critical (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (j : Gamma0EisensteinCuspClasses N) (t : ℝ) :
    AnalyticAt ℂ (gamma0CuspEisensteinCanonicalTest N (gamma0EisensteinCuspClassRepresentative N j) ψ)
      (eisensteinCriticalPoint t) := by
  let f := gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N j) ψ
  have h := meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ (eisensteinCriticalPoint t))
  apply h.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn
    (fun s _ => gamma0CuspEisensteinMeromorphicTest_meromorphic N
      (gamma0EisensteinCuspClassRepresentative N j) ψ s) (mem_univ _)]
  exact gamma0CuspEisensteinMeromorphicTest_order_all_critical N ψ j t

end ArtinMatthews
