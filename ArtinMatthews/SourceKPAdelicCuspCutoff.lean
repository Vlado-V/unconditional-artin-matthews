module

public import ArtinMatthews.SourceKPAdelicHighHeightFinite
public import ArtinMatthews.SourceKPAdelicCompactSection
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

/-! A concrete high-cusp cutoff of the actual rational Eisenstein sum.
Its rational support is finite at every argument for every spectral
parameter, and uniformly finite over compact adelic matrix sets. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing BigOperators ContDiff
noncomputable section

def sourceKPAdelicHeightCutoff (T h : ℝ) : ℝ := Real.smoothTransition (h/T-1)

theorem sourceKPAdelicHeightCutoff_zero {T h : ℝ} (hT : 0 < T) (hh : h ≤ T) :
    sourceKPAdelicHeightCutoff T h = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact sub_nonpos.mpr ((div_le_one hT).mpr hh)

theorem sourceKPAdelicHeightCutoff_one {T h : ℝ} (hT : 0 < T) (hh : 2*T ≤ h) :
    sourceKPAdelicHeightCutoff T h = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hd : 2 ≤ h/T := (le_div_iff₀ hT).mpr hh
  linarith

theorem sourceKPAdelicHeightCutoff_contDiff (T : ℝ) :
    ContDiff (ℝ) (∞ : ℕ∞ω) (sourceKPAdelicHeightCutoff T) := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.div_const T).sub contDiff_const)

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCutoffSeed (T : ℝ) (s : ℂ) : SourceKPRationalBorelFunction K hζ :=
  ⟨fun q => (sourceKPAdelicHeightCutoff T (sourceKPAdelicCoverHeight K hζ q) : ℂ) *
    sourceKPAdelicCompactScalar K hζ s q, by
      intro b hb q
      dsimp only
      rw [sourceKPAdelicCoverHeight_left_rationalBorel K hζ b hb q]
      congr 1
      exact (sourceKPAdelicPrincipalSeriesScalar K hζ s
        (sourceKPAdelicCompactSection K hζ s)).property b hb q⟩

def sourceKPAdelicCutoffEisenstein (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) : ℂ :=
  sourceKPAdelicRationalSum K hζ (sourceKPAdelicCutoffSeed K hζ T s) q

theorem sourceKPAdelicCutoffSummand_eq (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c =
      (sourceKPAdelicHeightCutoff T (sourceKPAdelicRationalHeight K hζ q c) : ℂ) *
        sourceKPAdelicRationalSummand K hζ
          (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s)) q c := by
  induction c using Quotient.inductionOn
  rfl

theorem sourceKPAdelicCutoffSummand_zero {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K)
    (hc : sourceKPAdelicRationalHeight K hζ q c ≤ T) :
    sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c = 0 := by
  rw [sourceKPAdelicCutoffSummand_eq, sourceKPAdelicHeightCutoff_zero hT hc,
    Complex.ofReal_zero, zero_mul]

theorem sourceKPAdelicCutoffSummand_entire (T : ℝ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Differentiable ℂ (fun s =>
      sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c) := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    change Differentiable ℂ (fun s =>
      (sourceKPAdelicHeightCutoff T (sourceKPAdelicCoverHeight K hζ
        (sourceKPAdelicProjectiveRationalLift K hζ γ*q)) : ℂ) *
          sourceKPAdelicCompactScalar K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ*q))
    exact (differentiable_const _).mul (sourceKPAdelicCompactScalar_entire K hζ _)

theorem sourceKPAdelicCutoffSummand_finite {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    Function.HasFiniteSupport
      (sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q) := by
  apply (sourceKPAdelicRationalHeight_finite K hζ q hT).subset
  intro c hc
  by_contra h
  exact hc (sourceKPAdelicCutoffSummand_zero K hζ hT s q c (le_of_not_gt h))

theorem sourceKPAdelicCutoffEisenstein_converges {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    Summable (sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q) :=
  summable_of_hasFiniteSupport (sourceKPAdelicCutoffSummand_finite K hζ hT s q)

theorem sourceKPAdelicCutoffEisenstein_entire {T : ℝ} (hT : 0 < T)
    (q : SourceKPAdelicProjective K hζ) :
    Differentiable ℂ (fun s => sourceKPAdelicCutoffEisenstein K hζ T s q) := by
  let I := (sourceKPAdelicRationalHeight_finite K hζ q hT).toFinset
  have he (s : ℂ) : sourceKPAdelicCutoffEisenstein K hζ T s q =
      ∑ c ∈ I, sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c := by
    apply tsum_eq_sum
    intro c hc
    apply sourceKPAdelicCutoffSummand_zero K hζ hT s q c
    have hc' : ¬ T < sourceKPAdelicRationalHeight K hζ q c := by
      simpa only [I, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hc
    exact le_of_not_gt hc'
  simp_rw [he]
  exact Differentiable.fun_sum (fun c _ => sourceKPAdelicCutoffSummand_entire K hζ T q c)

theorem sourceKPAdelicCutoffEisenstein_rational (T : ℝ) (s : ℂ)
    (γ : PGL(2,K)) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCutoffEisenstein K hζ T s (sourceKPAdelicProjectiveRationalLift K hζ γ*q) =
      sourceKPAdelicCutoffEisenstein K hζ T s q :=
  sourceKPAdelicRationalSum_automorphy K hζ (sourceKPAdelicCutoffSeed K hζ T s) γ q

theorem sourceKPAdelicCutoffSeed_right (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    (sourceKPAdelicCutoffSeed K hζ T s).val (q*k.val) =
      (sourceKPAdelicCutoffSeed K hζ T s).val q := by
  change (sourceKPAdelicHeightCutoff T (sourceKPAdelicCoverHeight K hζ (q*k.val)) : ℂ) *
      sourceKPAdelicCompactScalar K hζ s (q*k.val) = _
  rw [sourceKPAdelicCoverHeight_right_deep]
  congr 1
  exact congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => (f.val q).val 1)
    (sourceKPAdelicCompactSection_right K hζ s k)

theorem sourceKPAdelicCutoffEisenstein_right (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicCutoffEisenstein K hζ T s (q*k.val) =
      sourceKPAdelicCutoffEisenstein K hζ T s q := by
  apply tsum_congr
  intro c
  induction c using Quotient.inductionOn with
  | _ γ =>
    change (sourceKPAdelicCutoffSeed K hζ T s).val
      (sourceKPAdelicProjectiveRationalLift K hζ γ*(q*k.val)) = _
    rw [← mul_assoc, sourceKPAdelicCutoffSeed_right]
    rfl

theorem sourceKPAdelicCutoffSummand_uniform_finite {T : ℝ} (hT : 0 < T)
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ I : Set (SourceKPRationalBorelCoset K), I.Finite ∧
      ∀ s : ℂ, ∀ g ∈ S, ∀ q : SourceKPAdelicProjective K hζ,
        sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
        ∀ c ∉ I,
          sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c = 0 := by
  obtain ⟨I,hI,hbound⟩ := sourceKPAdelicRationalHeight_finite_on_compact K hζ S hS hT
  refine ⟨I,hI,fun s g hg q hq c hc => ?_⟩
  apply sourceKPAdelicCutoffSummand_zero K hζ hT s q c
  by_contra h
  exact hc (hbound g hg q hq c (lt_of_not_ge h))

end
end ArtinMatthews
