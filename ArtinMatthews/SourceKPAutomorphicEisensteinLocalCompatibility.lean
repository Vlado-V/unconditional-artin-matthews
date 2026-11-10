module

public import ArtinMatthews.SourceKPAutomorphicEisensteinLocalL2
public import ArtinMatthews.SourceKPAutomorphicEisensteinResidue
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

/-! The actual continuation germs are independent of the incoming cutoff, and
the exceptional pole is already visible on a concrete compact height sublevel. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField AdeleRing MatrixGroups Topology InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "L" => SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)
local notation "HY" => sourceKPAutomorphicCompactOrbitHeight K hζ

theorem sourceKPAutomorphicEisensteinLocalL2_ae {T : ℝ} (hT : 1 ≤ T)
    (S : Set Y) (hS : IsCompact S) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    (sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS s : Y → ℂ) =ᵐ[μY]
      S.indicator (sourceKPAutomorphicCompactEisenstein K hζ s) :=
  sourceKPAutomorphicEisensteinLocalL2_ae_of_initial K hζ hT S hS
    (sourceKPAutomorphicTruncatedContinuation_ae K hζ hT hs)

theorem sourceKPAutomorphicEisensteinLocalL2_cutoff_independent {T T' : ℝ}
    (hT : 1 ≤ T) (hT' : 1 ≤ T') (S : Set Y) (hS : IsCompact S) {s : ℂ} (hs : 0 < s.re) :
    sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS =ᶠ[𝓝[≠] s]
      sourceKPAutomorphicEisensteinLocalL2 K hζ hT' S hS := by
  let F := sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS
  let G := sourceKPAutomorphicEisensteinLocalL2 K hζ hT' S hS
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsPreconnected U :=
    ((convex_Ioi (𝕜 := ℝ) (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hm : MeromorphicOn (F-G) U :=
    (sourceKPAutomorphicEisensteinLocalL2_meromorphic K hζ hT S hS).sub
      (sourceKPAutomorphicEisensteinLocalL2_meromorphic K hζ hT' S hS)
  let d : ℝ := ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ)
  have hd : 0 < d := by dsimp only [d]; positivity
  let a : ℂ := d
  have ha : a ∈ U := by change 0 < a.re; simpa only [a,Complex.ofReal_re] using hd
  have ha' : d/2 < a.re := by simp only [a,Complex.ofReal_re]; linarith
  have he : (F-G) =ᶠ[𝓝[≠] a] 0 := by
    filter_upwards [((Complex.continuous_re.tendsto a).eventually (Ioi_mem_nhds ha')).filter_mono
      nhdsWithin_le_nhds] with z hz
    have hz' : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*z.re+1 := by
      change d ≤ 2*z.re+1
      linarith
    change F z-G z = 0
    apply sub_eq_zero.mpr
    apply Lp.ext
    exact (sourceKPAutomorphicEisensteinLocalL2_ae K hζ hT S hS hz').trans
      (sourceKPAutomorphicEisensteinLocalL2_ae K hζ hT' S hS hz').symm
  have h := hm.meromorphicOrderAt_eq_top_of_isPreconnected hU ha hs
    (meromorphicOrderAt_eq_top_iff.mpr he)
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp h] with z hz
  exact sub_eq_zero.mp hz

theorem sourceKPAutomorphicEisensteinLocalL2_explicit_pole {T : ℝ} (hT : 1 ≤ T) :
    let S : Set Y := {y | HY y ≤ 2*T+1}
    let hS : IsCompact S := sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ (2*T+1)
    meromorphicOrderAt (sourceKPAutomorphicEisensteinLocalL2 K hζ hT S hS) (1/6) = -1 := by
  dsimp only
  let S : Set Y := {y | HY y ≤ 2*T+1}
  have hS : IsCompact S := sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ (2*T+1)
  apply sourceKPAutomorphicEisensteinLocalL2_order K hζ hT S hS
  let qf := (sourceKPCoupledWildWeyl K hζ).2
  let b := (sourceKPFiniteLevelMk K hζ (1,qf)).2
  let W := sourceKPSelectedCuspWeight K hζ b (2*T) (2*T+1)
  let u := sourceKPAutomorphicExceptionalResidue K hζ hT
  have hA : 1 ≤ 2*T := by linarith
  have hAB : 2*T < 2*T+1 := by linarith
  obtain ⟨_,_,_,_,_,h⟩ := sourceKPAutomorphicExceptionalResidue_band K hζ hT le_rfl hA hAB
  change sourceKPGenuineAutomorphicL2Pairing K hζ W
    (sourceKPSelectedCuspWeight_memLp K hζ b (B := 2*T+1) hA) u ≠ 0 at h
  intro hz
  apply h
  rw [sourceKPGenuineAutomorphicL2Pairing_apply K hζ _ u
    (F := (u.val : Y → ℂ)) EventuallyEq.rfl]
  have ha := sourceKPAutomorphicGenuineCompactCutL2_coe K hζ S hS u
  change sourceKPAutomorphicGenuineCompactCutL2 K hζ S hS u = 0 at hz
  rw [hz] at ha
  have hzero : (0 : Y → ℂ) =ᵐ[μY] S.indicator (u.val : Y → ℂ) :=
    (Lp.coeFn_zero ℂ 2 μY).symm.trans ha
  calc
    _ = ∫ _ : Y, (0 : ℂ) ∂μY := by
      apply integral_congr_ae
      filter_upwards [hzero] with y hy
      change (0 : ℂ) = S.indicator (u.val : Y → ℂ) y at hy
      by_cases hyS : y ∈ S
      · rw [Set.indicator_of_mem hyS] at hy
        rw [← hy,mul_zero]
      · have hw : W y = 0 := by
          by_contra hn
          exact hyS (sourceKPSelectedCuspWeight_support K hζ b hA hn).2
        rw [hw,star_zero,zero_mul]
    _ = 0 := by simp

end
end ArtinMatthews
