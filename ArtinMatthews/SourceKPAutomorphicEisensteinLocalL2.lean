module

public import ArtinMatthews.SourceKPAutomorphicCompactTruncated
public import ArtinMatthews.SourceKPCompactCutoffL2Parameter
public import ArtinMatthews.L2MeasurableCutoff
public import ArtinMatthews.SourceKPAutomorphicSpectralFamily
public import ArtinMatthews.SourceKPAutomorphicCompactTopology
public import ArtinMatthews.SourceKPAutomorphicSpectralContinuation
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
public import OAI.NumberTheory.DirichletL.Eisenstein.MeromorphicResolvent


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full series continues on every compact Haar-L² restriction. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField AdeleRing MatrixGroups Topology InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "L" => SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ

def sourceKPAutomorphicGenuineCompactCutL2 (S : Set Y) (hS : IsCompact S) : H →L[ℂ] L :=
  (measurableL2Cutoff μY S hS.measurableSet).comp
    (sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)).subtypeL

theorem sourceKPAutomorphicGenuineCompactCutL2_coe (S : Set Y) (hS : IsCompact S) (u : H) :
    (sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS u : Y → ℂ) =ᵐ[μY]
      S.indicator (u.val : Y → ℂ) :=
  measurableL2Cutoff_coe μY S hS.measurableSet u.val

def sourceKPAutomorphicEisensteinLocalL2 {T : ℝ} (hT : 1 ≤ T) (S : Set Y) (hS : IsCompact S)
    (s : ℂ) : L :=
  sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2 K hζ (zero_lt_one.trans_le hT) S hS s +
    sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS
      (sourceKPAutomorphicTruncatedContinuation K hζ hT s)

theorem sourceKPAutomorphicEisensteinLocalL2_ae_of_initial {T : ℝ} (hT : 1 ≤ T)
    (S : Set Y) (hS : IsCompact S) {s : ℂ}
    (hu : ((sourceKPAutomorphicTruncatedContinuation K hζ hT s : L) : Y → ℂ) =ᵐ[μY]
      sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) :
    (sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS s : Y → ℂ) =ᵐ[μY]
      S.indicator (sourceKPAutomorphicCompactEisenstein K hζ s) := by
  let P := sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2 K hζ (zero_lt_one.trans_le hT) S hS s
  let U := sourceKPAutomorphicTruncatedContinuation K hζ hT s
  let C := sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS
  change ((P+C U : L) : Y → ℂ) =ᵐ[μY] _
  filter_upwards [Lp.coeFn_add P (C U),
    sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2_coe K hζ (zero_lt_one.trans_le hT) S hS s,
    sourceKPAutomorphicGenuineCompactCutL2_coe K hζ S hS U,
    hu] with y hsum hP hU hy
  change (P+C U) y = P y+(C U) y at hsum
  rw [hsum,hP,hU]
  by_cases h : y ∈ S
  · change U.val y = sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s y at hy
    rw [Set.indicator_of_mem h,Set.indicator_of_mem h,Set.indicator_of_mem h,hy,
      sourceKPAutomorphicCompactTruncatedEisenstein]
    ring
  · simp only [Set.indicator_of_notMem h,add_zero]

theorem sourceKPAutomorphicEisensteinLocalL2_meromorphic {T : ℝ} (hT : 1 ≤ T)
    (S : Set Y) (hS : IsCompact S) :
    MeromorphicOn (sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS) {s | 0 < s.re} := by
  intro s hs
  exact (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2_analyticAt K hζ
    (zero_lt_one.trans_le hT) S hS s).meromorphicAt.add
      (OAI.CubicEisenstein.meromorphicAt_clm (sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS)
        (sourceKPAutomorphicTruncatedContinuation_meromorphic K hζ hT s hs))

def sourceKPAutomorphicEisensteinLocalL2Regularized {T : ℝ} (hT : 1 ≤ T)
    (S : Set Y) (hS : IsCompact S) (s : ℂ) : L :=
  (s-1/6) • sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2 K hζ (zero_lt_one.trans_le hT) S hS s +
    sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS
      (sourceKPAutomorphicExceptionalRegularized K hζ hT s)

theorem sourceKPAutomorphicEisensteinLocalL2Regularized_analyticAt {T : ℝ} (hT : 1 ≤ T)
    (S : Set Y) (hS : IsCompact S) :
    AnalyticAt ℂ (sourceKPAutomorphicEisensteinLocalL2Regularized K hζ hT S hS) (1/6) := by
  have h₀ : AnalyticAt ℂ (fun s : ℂ => s-1/6) (1/6) := analyticAt_id.sub analyticAt_const
  have h := h₀.smul
    (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2_analyticAt K hζ
      (zero_lt_one.trans_le hT) S hS (1/6))
  exact h.add (((sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS).analyticAt
    (sourceKPAutomorphicExceptionalRegularized K hζ hT (1/6))).comp_of_eq
      (sourceKPAutomorphicExceptionalRegularized_analyticAt K hζ hT) rfl)

theorem sourceKPAutomorphicEisensteinLocalL2Regularized_value {T : ℝ} (hT : 1 ≤ T)
    (S : Set Y) (hS : IsCompact S) :
    sourceKPAutomorphicEisensteinLocalL2Regularized K hζ hT S hS (1/6) =
      sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS (sourceKPAutomorphicExceptionalResidue K hζ hT) := by
  rw [sourceKPAutomorphicEisensteinLocalL2Regularized,sub_self,zero_smul,zero_add,
    sourceKPAutomorphicExceptionalRegularized_value]

theorem sourceKPAutomorphicEisensteinLocalL2Regularized_eventually_eq {T : ℝ} (hT : 1 ≤ T)
    (S : Set Y) (hS : IsCompact S) :
    sourceKPAutomorphicEisensteinLocalL2Regularized K hζ hT S hS =ᶠ[𝓝[≠] (1/6 : ℂ)]
      fun s => (s-1/6) • sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS s := by
  filter_upwards [sourceKPAutomorphicExceptionalRegularized_eventually_eq K hζ hT] with s hs
  rw [sourceKPAutomorphicEisensteinLocalL2Regularized,sourceKPAutomorphicEisensteinLocalL2,
    hs,map_smul,smul_add]

theorem sourceKPAutomorphicEisensteinLocalL2_residue_tendsto {T : ℝ} (hT : 1 ≤ T)
    (S : Set Y) (hS : IsCompact S) :
    Tendsto (fun s => (s-1/6) • sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS s)
      (𝓝[≠] (1/6 : ℂ))
      (𝓝 (sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS (sourceKPAutomorphicExceptionalResidue K hζ hT))) := by
  have h := (sourceKPAutomorphicEisensteinLocalL2Regularized_analyticAt K hζ hT S hS).continuousAt
  rw [ContinuousAt,sourceKPAutomorphicEisensteinLocalL2Regularized_value] at h
  exact (h.mono_left nhdsWithin_le_nhds).congr'
    (sourceKPAutomorphicEisensteinLocalL2Regularized_eventually_eq K hζ hT S hS)

theorem sourceKPAutomorphicEisensteinLocalL2_order {T : ℝ} (hT : 1 ≤ T)
    (S : Set Y) (hS : IsCompact S)
    (hres : sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS
      (sourceKPAutomorphicExceptionalResidue K hζ hT) ≠ 0) :
    meromorphicOrderAt (sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS) (1/6) = -1 := by
  have hm : MeromorphicAt (sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS) (1/6) :=
    sourceKPAutomorphicEisensteinLocalL2_meromorphic K hζ hT S hS _ (by norm_num)
  apply (meromorphicOrderAt_eq_int_iff hm (n := -1)).mpr
  refine ⟨sourceKPAutomorphicEisensteinLocalL2Regularized K hζ hT S hS,
    sourceKPAutomorphicEisensteinLocalL2Regularized_analyticAt K hζ hT S hS,?_,?_⟩
  · rwa [sourceKPAutomorphicEisensteinLocalL2Regularized_value]
  · filter_upwards [sourceKPAutomorphicEisensteinLocalL2Regularized_eventually_eq K hζ hT S hS,
      self_mem_nhdsWithin] with s h hs
    have hne : s - (1/6 : ℂ) ≠ 0 := sub_ne_zero.mpr hs
    change sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS s =
      (s-1/6)^(-1 : ℤ) • sourceKPAutomorphicEisensteinLocalL2Regularized K hζ hT S hS s
    rw [h,zpow_neg_one,smul_smul,inv_mul_cancel₀ hne,one_smul]

end
end ArtinMatthews
