module

public import ArtinMatthews.GiantComparisonArcMellin
public import ArtinMatthews.GiantComparisonCutoffRows
public import ArtinMatthews.GiantComparisonEndpointGlobalMoment
public import ArtinMatthews.GiantComparisonMellinTail
public import ArtinMatthews.SourceComparisonActualLowTime
public import ArtinMatthews.GiantComparisonArcCore
public import ArtinMatthews.GiantComparisonArcEnergyJoin
public import ArtinMatthews.SourceComparisonLowTimeIntegral
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Insert the proved low-frequency estimate into the exact arc energy.
The only analytic input here is the remaining literal high band. -/
namespace ArtinMatthews

open Filter MeasureTheory Set
open scoped ContDiff
noncomputable section

universe u v
variable {I : Type u} [Fintype I]

theorem giantComparisonActualArcEnergy_eventually_of_high
    (e : I → ℝ) (he : ∀ i, (1/10 : ℝ) < e i ∧ e i < 1/5)
    (hinj : Function.Injective e) (m : ℕ) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {lo hi B : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) (hB : hi < B)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ Icc lo hi)
    (C D S A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G] (i : G ↪ GiantCandidateGroupIndex x)
      (t : G → ℕ), (∀ g, t g ≤ m) →
      ∀ (q : G → ℝ), (∀ g, 0 ≤ q g ∧ q g ≤ 1) →
      ∀ (b : ((g : G) → Fin (t g) → ℕ) → ℂ),
        (∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t, ‖b l‖ ≤ 1) →
      ∀ (Y σ : ℝ), x ≤ Y → Y ≤ x ^ (1 + ε/4) → |σ| ≤ (Real.log x)^D →
      ∀ (r : ℚ), (r.den : ℝ) ≤ (Real.log x)^C →
      ∀ T : ℝ,
        (∫ τ in {τ : ℝ | (Real.log x)^S ≤ |τ| ∧ |τ| ≤ T},
          ‖@sourceComparisonCenteredMellinSum I G _ _ e ε x Y σ B ψ
            (giantCandidateGroup x ∘ i) t q b r.den ⟨r.den_ne_zero⟩ r.num τ‖ ^ 2) ≤
          (Real.log x)^(-(A+1)) →
        (∫ τ in Icc (-T) T, ‖(Y : ℂ)⁻¹ *
          giantComparisonMellinPolynomial (giantComparisonCutoffRows Y lo hi)
            (giantComparisonArcTwist (r : ℝ) (giantCandidateComparisonLeftEndpoint
              e ε x Y σ ψ (giantCandidateGroup x ∘ i) t q b)) τ‖ ^ 2) ≤
          (Real.log x)^(-A) := by
  have hψ₁ : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hc : HasCompactSupport ψ :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuous hψ.continuous
  obtain ⟨K₁, hK₁⟩ := hc.deriv.exists_bound_of_continuous
    (hψ₁.continuous_deriv (by norm_num))
  let E := max S D
  filter_upwards [sourceComparisonCenteredMellinSum_lowTime_integral_eventually.{u,v} e he hinj m
    hε hεq hlo hlohi hB C E 1 (A+1),
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max K K₁)] with x hlow hx hL hKK
  intro G _ i t ht q hq b hb Y σ hYlo hYhi hσ r hr T hhigh
  let _ : NeZero r.den := ⟨r.den_ne_zero⟩
  let P := giantCandidateGroup x ∘ i
  let f := sourceComparisonCenteredMellinSum e ε x Y σ B ψ P t q b r.den r.num
  let L := Real.log x
  have hL₁ : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 2).trans hL
  have hR : L^S ≤ L^E := Real.rpow_le_rpow_of_exponent_le hL₁ (le_max_left S D)
  have hσ' : |σ| ≤ L^E := hσ.trans (Real.rpow_le_rpow_of_exponent_le hL₁ (le_max_right S D))
  have hx' : x ^ (1 - ε/4) ≤ x := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (show 1 - ε/4 ≤ 1 by linarith)
  have hY : 0 < Y := zero_lt_one.trans_le (hx.trans hYlo)
  have hzero (z : ℝ) (hz : z ∉ Icc lo hi) : ψ z = 0 :=
    Function.notMem_support.mp (fun h => hz (hs h))
  have hlow' := hlow i t ht q hq b hb Y σ (hx'.trans hYlo) hYhi hσ'
    ψ hψ₁ hzero (fun z => by rw [Real.rpow_one]; exact (hK z).trans ((le_max_left K K₁).trans hKK))
    (fun z => by rw [Real.rpow_one]; exact (hK₁ z).trans ((le_max_right K K₁).trans hKK))
    r.den hr r.num
  have hf : Continuous f :=
    sourceComparisonCenteredMellinSum_continuous e ε x Y σ B ψ P t q b r.den r.num
  have hsmall : (∫ τ in Icc (-(L^S)) (L^S), ‖f τ‖ ^ 2) ≤ L^(-A-1) := by
    have hh := (setIntegral_mono_set
      ((hf.norm.pow 2).integrableOn_Icc (μ := volume) (a := -(L^E)) (b := L^E))
      (Eventually.of_forall fun τ => sq_nonneg ‖f τ‖)
      (Eventually.of_forall fun _ h => Icc_subset_Icc (neg_le_neg hR) hR h)).trans hlow'
    rwa [show -(A+1) = -A-1 by ring] at hh
  have hbig : (∫ τ in {τ : ℝ | L^S ≤ |τ| ∧ |τ| ≤ T}, ‖f τ‖ ^ 2) ≤ L^(-A-1) := by
    simpa only [show -(A+1) = -A-1 by ring] using hhigh
  let g (τ : ℝ) := (Y : ℂ)⁻¹ * giantComparisonMellinPolynomial
    (giantComparisonCutoffRows Y lo hi)
    (giantComparisonArcTwist (r : ℝ) (giantCandidateComparisonLeftEndpoint e ε x Y σ ψ P t q b)) τ
  have hg : g = f := funext fun τ =>
    giantComparisonArcCore_eq_centeredMellinSum e ε x σ τ ψ P t q b r hY hB.le hs
  change (∫ τ in Icc (-T) T, ‖g τ‖ ^ 2) ≤ L^(-A)
  rw [hg]
  exact giantComparison_arcEnergy_log_join f hf hL hsmall hbig

end
end ArtinMatthews
