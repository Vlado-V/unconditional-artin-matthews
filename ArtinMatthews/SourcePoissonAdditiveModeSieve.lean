module

public import ArtinMatthews.SourcePoissonProbeRowBox
public import ArtinMatthews.SourceAdditiveCompactBox
public import ArtinMatthews.SourcePoissonAdditiveMass
public import ArtinMatthews.SourceReducedFractionTraceLift
public import ArtinMatthews.SourceAdditiveFractionsSigned
public import ArtinMatthews.SourcePoissonReducedGauss
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "OS" => sourceRing F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀
local notation "ha" => sourcePrimeExponentGenerator_ne_zero F hζ S₀
local notation "L" => SourceReducedFractionLabel F S₀ a

def sourcePoissonAdditiveLabels {Y : ℝ} (hY : 0 < Y) : Finset L :=
  (sourcePoissonLogSupportedExponents F S₀ hY).sigma
    (fun e => (sourcePoissonQuotientUnitFintype F S₀ hζ e).elems)

private theorem sourcePoissonAdditiveLabels_sum {Y : ℝ} (hY : 0 < Y)
    {A : Type} [AddCommMonoid A] (f : L → A) :
    (∑ p ∈ sourcePoissonAdditiveLabels F S₀ hζ hY, f p) =
      ∑ e ∈ sourcePoissonLogSupportedExponents F S₀ hY,
        ∑ d ∈ (sourcePoissonQuotientUnitFintype F S₀ hζ e).elems, f ⟨e, d⟩ :=
  Finset.sum_sigma _ _ f

def sourcePoissonAdditiveLabelWeight (Y : ℝ) (j : ℤ) (p : L) : ℂ :=
  (Y : ℂ)⁻¹ * (sourcePoissonQuotientResidue F S₀ hζ p.1 p.2.val /
    (Real.sqrt (q p.1 : ℝ) : ℂ)) * sourceProbeLogFourierPhase ((q p.1 : ℝ) / Y) j

theorem sourcePoissonAdditiveLabel_bound {Y : ℝ} (hY : 0 < Y) (p : L)
    (hp : p ∈ sourcePoissonAdditiveLabels F S₀ hζ hY) :
    (q p.1 : ℝ) ≤ (5 / 2 : ℝ) * Y := by
  have he : p.1 ∈ sourcePoissonLogSupportedExponents F S₀ hY := (Finset.mem_sigma.mp hp).1
  exact (div_le_iff₀ hY).mp (sourcePoissonLogSupportedExponents_ratio_mem F S₀ hY p.1 he).2

set_option backward.isDefEq.respectTransparency false in
theorem sourcePoissonLogAdditiveMode_eq_fractionSum {Y : ℝ} (hY : 0 < Y) (j : ℤ) (m : OS) :
    sourcePoissonLogAdditiveMode F S₀ hζ hY j m =
      ∑ p ∈ sourcePoissonAdditiveLabels F S₀ hζ hY,
        sourcePoissonAdditiveLabelWeight F S₀ hζ Y j p *
          sourceReducedFractionPhase F S₀ a ha p (-m) := by
  unfold sourcePoissonLogAdditiveMode
  rw [sourcePoissonAdditiveLabels_sum F S₀ hζ hY, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  let := sourcePoissonQuotientUnitFintype F S₀ hζ e
  rw [sourcePoissonOriginalGauss_eq_sum_units F S₀ hζ e (-m), Finset.sum_div,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  unfold sourcePoissonAdditiveLabelWeight
  ring

/-- Every separated mode has total coefficient square mass at most C/Y. -/
theorem exists_sourcePoissonAdditiveLabelWeight_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ {Y : ℝ} (hY : 1 ≤ Y) (j : ℤ),
      (∑ p ∈ sourcePoissonAdditiveLabels F S₀ hζ (lt_of_lt_of_le zero_lt_one hY),
        ‖sourcePoissonAdditiveLabelWeight F S₀ hζ Y j p‖ ^ 2) ≤ C / Y := by
  obtain ⟨C, hC, hb⟩ := exists_sourcePoissonSupportedExponent_card_le F S₀
  refine ⟨C, hC, ?_⟩
  intro Y hY j
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY
  let P := sourcePoissonLogSupportedExponents F S₀ hY₀
  have hp : (P.card : ℝ) ≤ C * Y :=
    hb Y P hY (fun e he => (div_le_iff₀ hY₀).mp
      (sourcePoissonLogSupportedExponents_ratio_mem F S₀ hY₀ e he).2)
  have hm (e : SourcePrimeExponents F S₀) :
      (∑ d ∈ (sourcePoissonQuotientUnitFintype F S₀ hζ e).elems,
        ‖sourcePoissonAdditiveLabelWeight F S₀ hζ Y j ⟨e, d⟩‖ ^ 2) ≤ (Y ^ 2)⁻¹ :=
    sourcePoissonQuotientUnit_mass F S₀ hζ e Y hY₀
      (sourceProbeLogFourierPhase ((q e : ℝ) / Y) j)
      (sourceProbeLogFourierPhase_norm ((q e : ℝ) / Y) j).le
  have hreal : (∑ _ ∈ P, (Y ^ 2)⁻¹) ≤ C / Y := by
    calc
      _ = (P.card : ℝ) * (Y ^ 2)⁻¹ := by simp
      _ ≤ (C * Y) * (Y ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = C / Y := by field_simp
  exact (le_of_eq (sourcePoissonAdditiveLabels_sum F S₀ hζ hY₀
    (fun p => ‖sourcePoissonAdditiveLabelWeight F S₀ hζ Y j p‖ ^ 2))).trans
    ((Finset.sum_le_sum (fun e _ => hm e)).trans hreal)

variable [IsTotallyComplex F]

theorem exists_sourcePoissonLogAdditiveMode_sieve (htrace : traceBadPlaces F ⊆ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y : ℝ) (hY : 1 ≤ Y), Y ≤ X →
      ∀ (M : Finset OS), (∀ m ∈ M,
        m ∈ sourceScaledLatticeRows F S₀ hζ (sourcePoissonLogRowBox F S₀ hζ) (X * Y)) →
      ∀ j : ℤ,
      (∑ m ∈ M, ‖sourcePoissonLogAdditiveMode F S₀ hζ (zero_lt_one.trans_le hY) j m‖ ^ 2) ≤
      C * (X * Y) / Y := by
  obtain ⟨Cs, hCs, hs⟩ := sourceFixedProductSignedAdditiveSieve F S₀ hζ htrace
    (sourcePoissonLogRowBox F S₀ hζ) (sourcePoissonLogRowBox_isCompact F S₀ hζ)
  obtain ⟨Cm, hCm, hm⟩ := exists_sourcePoissonAdditiveLabelWeight_mass F S₀ hζ
  refine ⟨Cs * Cm * (29 / 4), by positivity, ?_⟩
  intro X Y hY hXY M hM j
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY
  have hX : 1 ≤ X := hY.trans hXY
  have hN : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hX hY
  have hV : 1 ≤ (5 / 2 : ℝ) * Y :=
    one_le_mul_of_one_le_of_one_le (by norm_num) hY
  let P := sourcePoissonAdditiveLabels F S₀ hζ hY₀
  let b := sourcePoissonAdditiveLabelWeight F S₀ hζ Y j
  have h := hs (X * Y) ((5 / 2 : ℝ) * Y) hN hV M P hM
    (sourcePoissonAdditiveLabel_bound F S₀ hζ hY₀) b
  have hmode (m : OS) :
      (∑ p ∈ P, b p * sourceReducedFractionPhase F S₀ a ha p (-m)) =
        sourcePoissonLogAdditiveMode F S₀ hζ hY₀ j m :=
    (sourcePoissonLogAdditiveMode_eq_fractionSum F S₀ hζ hY₀ j m).symm
  simp only [hmode] at h
  have hsize : X * Y + ((5 / 2 : ℝ) * Y) ^ 2 ≤ (29 / 4 : ℝ) * (X * Y) := by
    nlinarith [mul_le_mul_of_nonneg_right hXY hY₀.le]
  calc
    _ ≤ Cs * (X * Y + ((5 / 2 : ℝ) * Y) ^ 2) * (Cm / Y) :=
      h.trans (mul_le_mul_of_nonneg_left (hm hY j) (by positivity))
    _ ≤ (Cs * ((29 / 4 : ℝ) * (X * Y))) * (Cm / Y) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hCs.le) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
