module

public import ArtinMatthews.SourceKPAdelicCutoffCasimirSum
public import ArtinMatthews.SourceKPAdelicCutoffDefect
public import ArtinMatthews.SourceKPAdelicKernelContinuity
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

/-! Pointwise entire dependence and full compact invariance of the
literal Casimir defect of the actual cusp cutoff. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCutoffCasimirTerm_entire (T : ℝ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (c : SourceKPRationalBorelCoset K) :
    Differentiable ℂ (fun s => sourceKPAdelicCutoffCasimirTerm K hζ T s q v c) := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    change Differentiable ℂ (fun s => sourceKPAdelicCutoffCasimirTerm K hζ T s q v
      (sourceKPRationalBorelCosetMk K γ))
    let a := sourceKPAdelicProjectiveRationalLift K hζ γ*q
    let H := sourceKPAdelicCoverHeight K hζ a
    let φ := sourceKPAdelicHeightCutoff T
    have he : (fun s => sourceKPAdelicCutoffCasimirTerm K hζ T s q v
        (sourceKPRationalBorelCosetMk K γ)) = fun s =>
          ((1-4*s^2)*(φ H : ℂ) - (4*H^2*deriv (deriv φ) H : ℝ) -
            (8*s+4)*(H : ℂ)*((deriv φ H : ℝ) : ℂ))*sourceKPAdelicCompactScalar K hζ s a := by
      funext s
      rw [sourceKPAdelicCutoffCasimirTerm_mk,
        sourceKPAdelicRadialSection_casimir K hζ _ s
          ((sourceKPAdelicHeightCutoff_contDiff T).of_le (by simp))]
      unfold sourceKPAdelicRadialSection
      dsimp only [a,H,φ]
      ring
    rw [he]
    apply Differentiable.mul
    · fun_prop
    · exact sourceKPAdelicCompactScalar_entire K hζ a

theorem sourceKPAdelicCutoffCasimir_tsum {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v =
      ∑' c, sourceKPAdelicCutoffCasimirTerm K hζ T s q v c := by
  obtain ⟨J,hJ⟩ := sourceKPAdelicCutoffCasimir_finite K hζ hT q v
  exact (hJ s).1.trans (tsum_eq_sum (hJ s).2.2).symm

theorem sourceKPAdelicCutoffCasimir_entire {T : ℝ} (hT : 0 < T)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    Differentiable ℂ (fun s => sourceArchGlobalCasimir K hζ
      (sourceKPAdelicCutoffEisenstein K hζ T s) q v) := by
  obtain ⟨J,hJ⟩ := sourceKPAdelicCutoffCasimir_finite K hζ hT q v
  have he : (fun s => sourceArchGlobalCasimir K hζ
      (sourceKPAdelicCutoffEisenstein K hζ T s) q v) =
        fun s => ∑ c ∈ J, sourceKPAdelicCutoffCasimirTerm K hζ T s q v c :=
    funext (fun s => (hJ s).1)
  rw [he]
  exact Differentiable.fun_sum (fun c _ => sourceKPAdelicCutoffCasimirTerm_entire K hζ T q v c)

theorem sourceKPAdelicCutoffCasimirDefect_entire {T : ℝ} (hT : 0 < T)
    (q : SourceKPAdelicProjective K hζ) :
    Differentiable ℂ (fun s => sourceKPAdelicCutoffCasimirDefect K hζ T s q) := by
  unfold sourceKPAdelicCutoffCasimirDefect
  apply Differentiable.sub
  · exact Differentiable.fun_sum (fun v _ => sourceKPAdelicCutoffCasimir_entire K hζ hT q v)
  · apply Differentiable.mul
    · fun_prop
    · exact sourceKPAdelicCutoffEisenstein_entire K hζ hT q

theorem sourceKPAdelicRadialSection_casimir_right (φ : ℝ → ℝ) (s : ℂ)
    (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ) (q : SourceKPAdelicProjective K hζ)
    (k : sourceKPAdelicDeepCompact K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ (sourceKPAdelicRadialSection K hζ φ s) (q*k.val) v =
      sourceArchGlobalCasimir K hζ (sourceKPAdelicRadialSection K hζ φ s) q v := by
  rw [sourceKPAdelicRadialSection_casimir K hζ φ s hφ,
    sourceKPAdelicRadialSection_casimir K hζ φ s hφ]
  unfold sourceKPAdelicRadialSection
  rw [sourceKPAdelicCoverHeight_right_deep,sourceKPAdelicCompactScalar_right]

theorem sourceKPAdelicCutoffCasimirTerm_right (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ)
    (v : InfinitePlace K) (c : SourceKPRationalBorelCoset K) :
    sourceKPAdelicCutoffCasimirTerm K hζ T s (q*k.val) v c =
      sourceKPAdelicCutoffCasimirTerm K hζ T s q v c := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    change sourceKPAdelicCutoffCasimirTerm K hζ T s (q*k.val) v (sourceKPRationalBorelCosetMk K γ) =
      sourceKPAdelicCutoffCasimirTerm K hζ T s q v (sourceKPRationalBorelCosetMk K γ)
    rw [sourceKPAdelicCutoffCasimirTerm_mk,sourceKPAdelicCutoffCasimirTerm_mk,← mul_assoc]
    exact sourceKPAdelicRadialSection_casimir_right K hζ _ s
      ((sourceKPAdelicHeightCutoff_contDiff T).of_le (by simp)) _ k v

theorem sourceKPAdelicCutoffCasimir_right {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) (q*k.val) v =
      sourceArchGlobalCasimir K hζ (sourceKPAdelicCutoffEisenstein K hζ T s) q v := by
  rw [sourceKPAdelicCutoffCasimir_tsum K hζ hT,sourceKPAdelicCutoffCasimir_tsum K hζ hT]
  apply tsum_congr
  exact fun c => sourceKPAdelicCutoffCasimirTerm_right K hζ T s q k v c

theorem sourceKPAdelicCutoffCasimirDefect_right {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s (q*k.val) =
      sourceKPAdelicCutoffCasimirDefect K hζ T s q := by
  unfold sourceKPAdelicCutoffCasimirDefect
  simp_rw [sourceKPAdelicCutoffCasimir_right K hζ hT,
    sourceKPAdelicCutoffEisenstein_right K hζ T s]

end
end ArtinMatthews
