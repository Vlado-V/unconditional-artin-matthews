module

public import ArtinMatthews.MarkedMinorArcDirtyFreshGood
public import ArtinMatthews.MarkedMinorArcDirtyGoodRow
public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedMinorArcDirtyRawExpectation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Exact K-dependent raw-delta epsilon, independent of prime-band exponents. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def markedDirtyRawRowConstant (K : ℕ) (ρ : ℝ) : ℝ :=
  33*(1/(1-ρ)^2)^K*(2:ℝ)^K

theorem markedDirtyRawRowConstant_nonneg (K : ℕ) (ρ : ℝ) :
    0 ≤ markedDirtyRawRowConstant K ρ := by unfold markedDirtyRawRowConstant; positivity

theorem markedDirtyRaw_epsilon_bound {K i j M B : ℕ} {ρ L a : ℝ}
    (hi : i+1 ≤ K) (hj : j ≤ K) (hB : 1 ≤ B)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hL : 1 ≤ L) (ha : (1/10:ℝ) ≤ a) :
    33*(1/(1-ρ)^2)^i*(2:ℝ)^j*
        ((B:ℝ)*(M:ℝ)⁻¹^K+(B:ℝ)^(i+1)*Real.exp (-(L^a)/4)) ≤
      markedDirtyRawRowConstant K ρ*
        ((B:ℝ)*(M:ℝ)⁻¹^K+(B:ℝ)^K*Real.exp (-(L^(1/10:ℝ))/4)) := by
  have hC : 1 ≤ 1/(1-ρ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 1-ρ))).mpr
    nlinarith
  have hiK : i ≤ K := by omega
  have hcPow := pow_le_pow_right₀ hC hiK
  have htwoPow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj
  have hBpow := pow_le_pow_right₀ (by exact_mod_cast hB : (1:ℝ)≤B) hi
  have hExp : Real.exp (-(L^a)/4) ≤ Real.exp (-(L^(1/10:ℝ))/4) :=
    Real.exp_le_exp.mpr (by linarith [Real.rpow_le_rpow_of_exponent_le hL ha])
  unfold markedDirtyRawRowConstant
  gcongr

theorem markedRawDirty_delta_row_epsilon_eventually
    {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (eFresh : R → ℝ) (heFresh : ∀ j, (1/10:ℝ) ≤ eFresh j) :
    ∀ᶠ x : ℝ in atTop, ∀ (M B : ℕ)
      (source : MarkedRawActive (markedRawActualPrimeBand e x) M)
      (memory : MarkedRawMemory (markedRawActualPrimeBand e x) B) (jstar : J) (I : Finset J)
      (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z w : ℤ × ℤ)
      (Q : Finset ℤ) (r q ρ : ℝ) (newHits : (J → Fin M) → V → I → ℕ),
      0 < M → 1 ≤ B → I.card+1 ≤ Fintype.card J → Fintype.card R ≤ Fintype.card J → (∀ j, Function.Injective (source j)) →
      markedMinorIntegerDet z w=1 → markedMinorIntegerTau r z ≠ 0 →
      (∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16) →
      0 ≤ q → q ≤ 1 → 0 ≤ ρ → ρ < 1 →
      ((markedMinorIntegerTau r w/markedMinorIntegerTau r z:ℝ):AddCircle (1:ℝ)) ∉
        {s | Real.exp (-((Real.log x)^(e jstar))/4) ≤
          markedPairFailureProbability Q (markedFreshIntegerProduct eFresh x) (markedFreshHarmonicLaw eFresh x)
            (100*Real.exp (-((Real.log x)^(e jstar)))) s} →
      (∑ t : MarkedFreshPrimeTuple eFresh x, markedFreshTiltedLaw eFresh q x t *
        markedRawDirtyGoodChoiceMass source memory jstar I V hV z (markedFreshIntegerProduct eFresh x t)
          Q ρ newHits) ≤
        markedDirtyRawRowConstant (Fintype.card J) ρ*
          ((B:ℝ)*(M:ℝ)⁻¹^(Fintype.card J)+(B:ℝ)^(Fintype.card J)*
            Real.exp (-((Real.log x)^(1/10:ℝ))/4)) := by
  filter_upwards [markedRawDirty_delta_choice_expectation_eventually e hinj eFresh heFresh,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hrow hlog
  intro M B source memory jstar I V hV z w Q r q ρ newHits hM hB hI hR hdist hd hz hbox hq0 hq1 hρ0 hρ1 hroot
  exact (hrow M B source memory jstar I V hV z w Q r q ρ newHits hM hdist hd hz hbox hq0 hq1 hρ0 hρ1 hroot).trans
    (markedDirtyRaw_epsilon_bound hI hR hB hρ0 hρ1 hlog (he jstar))

end ArtinMatthews
