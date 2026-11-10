module

public import ArtinMatthews.SourceArchRightCasimir
public import ArtinMatthews.SourceKPAdelicCuspCutoff
public import ArtinMatthews.SourceKPAdelicOrbitHeight
public import ArtinMatthews.SourceArchDiagonalCompact
public import ArtinMatthews.SourceArchGlobalRightCasimir
public import ArtinMatthews.SourceKPAdelicArchHeightPaths
public import ArtinMatthews.SourceKPAdelicCutoffSupport
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

/-! The actual Casimir defect of the concrete cusp cutoff vanishes
outside a bounded rational-orbit height region. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Filter
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchGlobalCasimir_rational
    (f : SourceKPAdelicProjective K hζ → ℂ)
    (hf : ∀ γ : PGL(2,K), ∀ q, f (sourceKPAdelicProjectiveRationalLift K hζ γ*q) = f q)
    (γ : PGL(2,K)) (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ f (sourceKPAdelicProjectiveRationalLift K hζ γ*q) v =
      sourceArchGlobalCasimir K hζ f q v := by
  have hU (z : ℂ) : sourceArchGlobalUpperTranslate K hζ f
      (sourceKPAdelicProjectiveRationalLift K hζ γ*q) v z =
        sourceArchGlobalUpperTranslate K hζ f q v z := by
    funext t
    unfold sourceArchGlobalUpperTranslate
    rw [mul_assoc, hf]
  have hA : sourceArchGlobalDiagonalTranslate K hζ f
      (sourceKPAdelicProjectiveRationalLift K hζ γ*q) v =
        sourceArchGlobalDiagonalTranslate K hζ f q v := by
    funext t
    unfold sourceArchGlobalDiagonalTranslate
    rw [mul_assoc, hf]
  unfold sourceArchGlobalCasimir
  rw [hU 1, hU Complex.I, hA]

theorem sourceKPAdelicCutoff_upper_eventually_eq {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (z : ℂ)
    (hq : 2*T < sourceKPAdelicCoverHeight K hζ q) :
    sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v z =ᶠ[𝓝 0]
      sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicCompactScalar K hζ s) q v z := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, 2*T < sourceKPAdelicCoverHeight K hζ
      (q*sourceArchGroupSingle K hζ v (sourceKPUpperMatrix ℂ ((t : ℂ)*z))) :=
    (sourceKPAdelicCoverHeight_upper_continuous K hζ q v z).continuousAt
      (Ioi_mem_nhds (by simpa only [Complex.ofReal_zero, zero_mul, sourceKPUpperMatrix_zero,
        sourceArchGroupSingle_one, mul_one] using hq))
  filter_upwards [hh] with t ht
  exact sourceKPAdelicCutoffEisenstein_eq_of_high K hζ hT s _ ht.le

theorem sourceKPAdelicCutoff_diagonal_eventually_eq {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K)
    (hq : 2*T < sourceKPAdelicCoverHeight K hζ q) :
    sourceArchGlobalDiagonalTranslate K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v =ᶠ[𝓝 0]
      sourceArchGlobalDiagonalTranslate K hζ (sourceKPAdelicCompactScalar K hζ s) q v := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, 2*T < sourceKPAdelicCoverHeight K hζ
      (q*sourceArchGroupSingle K hζ v (sourceArchPositiveDiagonal t)) :=
    (sourceKPAdelicCoverHeight_diagonal_continuous K hζ q v).continuousAt
      (Ioi_mem_nhds (by simpa only [sourceArchPositiveDiagonal_zero,
        sourceArchGroupSingle_one, mul_one] using hq))
  filter_upwards [hh] with t ht
  exact sourceKPAdelicCutoffEisenstein_eq_of_high K hζ hT s _ ht.le

theorem sourceKPAdelicCutoff_casimir_of_high {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K)
    (hq : 2*T < sourceKPAdelicCoverHeight K hζ q) :
    sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v =
      (1-4*s^2)*sourceKPAdelicCutoffEisenstein K hζ T s q := by
  have h₁ := sourceKPAdelicCutoff_upper_eventually_eq K hζ hT s q v 1 hq
  have hI := sourceKPAdelicCutoff_upper_eventually_eq K hζ hT s q v Complex.I hq
  have hA := sourceKPAdelicCutoff_diagonal_eventually_eq K hζ hT s q v hq
  have he : sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v =
      sourceArchGlobalCasimir K hζ (sourceKPAdelicCompactScalar K hζ s) q v := by
    unfold sourceArchGlobalCasimir
    rw [h₁.deriv.deriv_eq, hI.deriv.deriv_eq, hA.deriv.deriv_eq, hA.deriv_eq]
  rw [he, sourceArchGlobalCasimir_compactScalar,
    sourceKPAdelicCutoffEisenstein_eq_of_high K hζ hT s q hq.le]

def sourceKPAdelicCutoffCasimirDefect (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) : ℂ :=
  (∑ v : InfinitePlace K,
    sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v) -
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)*sourceKPAdelicCutoffEisenstein K hζ T s q

theorem sourceKPAdelicCutoffCasimirDefect_rational (T : ℝ) (s : ℂ)
    (γ : PGL(2,K)) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s
      (sourceKPAdelicProjectiveRationalLift K hζ γ*q) =
        sourceKPAdelicCutoffCasimirDefect K hζ T s q := by
  unfold sourceKPAdelicCutoffCasimirDefect
  simp_rw [sourceArchGlobalCasimir_rational K hζ _
    (sourceKPAdelicCutoffEisenstein_rational K hζ T s),
    sourceKPAdelicCutoffEisenstein_rational]

theorem sourceKPAdelicCutoffCasimirDefect_of_high {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : 2*T < sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s q = 0 := by
  have := source_isTotallyComplex K hζ
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  unfold sourceKPAdelicCutoffCasimirDefect
  simp_rw [sourceKPAdelicCutoff_casimir_of_high K hζ hT s q _ hq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_assoc, sub_self]

theorem sourceKPAdelicCutoffCasimirDefect_support {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    Function.support (sourceKPAdelicCutoffCasimirDefect K hζ T s) ⊆
      {q : SourceKPAdelicProjective K hζ | sourceKPAdelicOrbitHeight K hζ q ≤ 2*T} := by
  intro q hq
  by_contra h
  have hsup : 2*T < sourceKPAdelicOrbitHeight K hζ q := lt_of_not_ge h
  obtain ⟨a,⟨γ,rfl⟩,hγ⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hsup
  have hz := sourceKPAdelicCutoffCasimirDefect_of_high K hζ hT s
    (sourceKPAdelicProjectiveRationalLift K hζ γ*q) hγ
  rw [sourceKPAdelicCutoffCasimirDefect_rational] at hz
  exact hq hz

end
end ArtinMatthews
