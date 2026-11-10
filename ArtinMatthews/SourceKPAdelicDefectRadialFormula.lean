module

public import ArtinMatthews.SourceKPAdelicCutoffCasimirSum
public import ArtinMatthews.SourceKPAdelicCutoffDefect
public import ArtinMatthews.SourceKPAdelicCutoffDefectParameter
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

/-! The literal defect is a finite rational sum of an explicit radial
multiplier. This form retains every finite-place scalar. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Filter
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators Topology
noncomputable section

def sourceKPAdelicDefectCoefficient (T : ℝ) (s : ℂ) (H : ℝ) : ℂ :=
  -(4*H^2*deriv (deriv (sourceKPAdelicHeightCutoff T)) H : ℝ) -
    (8*s+4)*(H : ℂ)*((deriv (sourceKPAdelicHeightCutoff T) H : ℝ) : ℂ)

theorem sourceKPAdelicDefectCoefficient_zero {T H : ℝ} (hT : 0 < T) (hH : H ≤ T/2) (s : ℂ) :
    sourceKPAdelicDefectCoefficient T s H = 0 := by
  have hlt : H < T := by linarith
  have he : sourceKPAdelicHeightCutoff T =ᶠ[𝓝 H] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hlt] with x hx
    exact sourceKPAdelicHeightCutoff_zero hT hx.le
  have hfirst : deriv (sourceKPAdelicHeightCutoff T) H = 0 := by
    simpa only [deriv_const] using he.deriv_eq
  have hsecond : deriv (deriv (sourceKPAdelicHeightCutoff T)) H = 0 := by
    simpa only [deriv_const'] using he.deriv.deriv_eq
  simp only [sourceKPAdelicDefectCoefficient,hfirst,hsecond,mul_zero,Complex.ofReal_zero,neg_zero,sub_zero]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicDefectTerm (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (c : SourceKPRationalBorelCoset K) : ℂ :=
  sourceKPAdelicDefectCoefficient T s (sourceKPAdelicRationalHeight K hζ q c) *
    sourceKPAdelicRationalSummand K hζ
      (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s)) q c

theorem sourceKPAdelicDefectTerm_finite {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    Function.HasFiniteSupport (sourceKPAdelicDefectTerm K hζ T s q) := by
  apply (sourceKPAdelicRationalHeight_finite K hζ q (by linarith : 0 < T/2)).subset
  intro c hc
  by_contra h
  have hle : sourceKPAdelicRationalHeight K hζ q c ≤ T/2 := le_of_not_gt h
  exact hc (by rw [sourceKPAdelicDefectTerm,sourceKPAdelicDefectCoefficient_zero hT hle,zero_mul])

theorem sourceKPAdelicDefectTerm_uniform_finite {T : ℝ} (hT : 0 < T)
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ I : Set (SourceKPRationalBorelCoset K), I.Finite ∧
      ∀ s g, g ∈ S → ∀ q : SourceKPAdelicProjective K hζ,
        sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
        ∀ c, c ∉ I → sourceKPAdelicDefectTerm K hζ T s q c = 0 := by
  obtain ⟨I,hI,hbound⟩ := sourceKPAdelicRationalHeight_finite_on_compact K hζ S hS (by linarith : 0 < T/2)
  refine ⟨I,hI,?_⟩
  intro s g hg q hq c hc
  have hle : sourceKPAdelicRationalHeight K hζ q c ≤ T/2 := by
    by_contra h
    exact hc (hbound g hg q hq c (lt_of_not_ge h))
  rw [sourceKPAdelicDefectTerm,sourceKPAdelicDefectCoefficient_zero hT hle,zero_mul]

theorem sourceKPAdelicCutoffCasimirTerm_eq (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (c : SourceKPRationalBorelCoset K) :
    sourceKPAdelicCutoffCasimirTerm K hζ T s q v c =
      (1-4*s^2)*sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c +
        sourceKPAdelicDefectTerm K hζ T s q c := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    change sourceKPAdelicCutoffCasimirTerm K hζ T s q v (sourceKPRationalBorelCosetMk K γ) = _
    rw [sourceKPAdelicCutoffCasimirTerm_mk,sourceKPAdelicRadialSection_casimir K hζ _ s
      ((sourceKPAdelicHeightCutoff_contDiff T).of_le (by simp))]
    rfl

theorem sourceKPAdelicCutoffCasimir_radial_sum {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v =
      (1-4*s^2)*sourceKPAdelicCutoffEisenstein K hζ T s q +
        ∑' c, sourceKPAdelicDefectTerm K hζ T s q c := by
  rw [sourceKPAdelicCutoffCasimir_tsum K hζ hT]
  simp_rw [sourceKPAdelicCutoffCasimirTerm_eq]
  rw [Summable.tsum_add ((sourceKPAdelicCutoffEisenstein_converges K hζ hT s q).mul_left _)
    (summable_of_hasFiniteSupport (sourceKPAdelicDefectTerm_finite K hζ hT s q)),tsum_mul_left]
  rfl

theorem sourceKPAdelicCutoffCasimirDefect_radial_sum {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s q =
      (InfinitePlace.nrComplexPlaces K : ℂ)*∑' c, sourceKPAdelicDefectTerm K hζ T s q c := by
  have := source_isTotallyComplex K hζ
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,IsTotallyComplex.nrRealPlaces_eq_zero,zero_add]
  rw [sourceKPAdelicCutoffCasimirDefect]
  simp_rw [sourceKPAdelicCutoffCasimir_radial_sum K hζ hT]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
  ring

end
end ArtinMatthews
