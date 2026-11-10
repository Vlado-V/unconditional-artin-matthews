module

public import ArtinMatthews.SourceReducedFractionLabels
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyCoordinates
public import ArtinMatthews.SourceFractionalIdealDualValuation
public import ArtinMatthews.SourceReducedFractionNorm
public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencySeparation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual lifted source fractions satisfy the hypotheses of the
checked modular Gaussian sieve in a fixed integral trace basis. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain AllowedGenerators FractionalIdeal
open StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "M" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F
local notation "O" => (⊤ : Ideal (𝓞 F))
local notation "coord" => idealModuleTraceCoordinates F O top_ne_bot
local notation "J" => IdealModuleFrequencyIndex F O top_ne_bot

/-- Integer translates in the actual trace coordinates preserve the
source separation, with the same reciprocal radius as the integral-ideal
sieve. The finite-place cut is the actual codifferent. -/
theorem sourceReducedFraction_traceCoordinates_separated
    (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e})
    (htrace : traceBadPlaces F ⊆ S) (δ : 𝓞 F) (hδ : δ ≠ 0)
    (hδS : ∀ P : HeightOneSpectrum (𝓞 F), P ∉ S → P.valuation F (δ : F) = 1)
    (p p' : SourceReducedFractionLabel F S₀ a) (hne : p ≠ p') (x x' : R)
    (hx : Ideal.Quotient.mk (Ideal.span {a p.1}) x = (p.2 : R ⧸ Ideal.span {a p.1}))
    (hx' : Ideal.Quotient.mk (Ideal.span {a p'.1}) x' = (p'.2 : R ⧸ Ideal.span {a p'.1}))
    (hβ : (x : F) / ((a p.1 : F) * (δ : F)) ∈ FractionalIdeal.dual ℤ ℚ (M p.1 : FI))
    (hβ' : (x' : F) / ((a p'.1 : F) * (δ : F)) ∈ FractionalIdeal.dual ℤ ℚ (M p'.1 : FI))
    {V : ℝ} (hp : (q p.1 : ℝ) ≤ V) (hp' : (q p'.1 : ℝ) ≤ V) (k : J → ℤ) :
    idealModuleCoordinateSeparationRadius F O top_ne_bot V ≤
      ‖coord ((x : F) / ((a p.1 : F) * (δ : F))) -
        coord ((x' : F) / ((a p'.1 : F) * (δ : F))) + fun j => (k j : ℝ)‖ := by
  let β := (x : F) / ((a p.1 : F) * (δ : F))
  let β' := (x' : F) / ((a p'.1 : F) * (δ : F))
  let r₀ := idealModuleTraceIntegerLift F O top_ne_bot k
  have hr₀ : r₀ ∈ FractionalIdeal.dual ℤ ℚ (1 : FI) := by
    have hr := idealModuleTraceIntegerLift_mem_dual F O top_ne_bot k
    rwa [FractionalIdeal.coeIdeal_top] at hr
  have hr (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ S) :
      P.valuation F (r₀ * (δ : F)) ≤ 1 := by
    rw [map_mul, hδS P hP, mul_one]
    have h := (sourceFractionalIdeal_dual_mem_iff F (1 : FI) one_ne_zero r₀).mp hr₀ P
    rw [(sourceDifferentExponent_eq_zero_iff F P).mpr (fun h => hP (htrace h)),
      FractionalIdeal.count_one, Int.natCast_zero, zero_add, WithZero.exp_zero] at h
    exact h
  let r : R := ⟨r₀ * (δ : F), hr⟩
  have hδF : (δ : F) ≠ 0 := Subtype.coe_injective.ne hδ
  have haF : (a p.1 : F) ≠ 0 := Subtype.coe_injective.ne (ha p.1)
  have haF' : (a p'.1 : F) ≠ 0 := Subtype.coe_injective.ne (ha p'.1)
  have hn : β - β' + r₀ ≠ 0 := by
    intro hz
    apply sourceReducedFraction_lifts_difference_ne_zero F S₀ a ha hgen p p' x x' r hx hx' hne
    calc
      _ = (β - β' + r₀) * (δ : F) := by
        dsimp only [β, β', r, Subtype.coe_mk]
        field_simp
      _ = 0 := by rw [hz, zero_mul]
  have hMv : (Ideal.absNorm (M p.1) : ℝ) ≤ V := by
    rw [sourcePrimeExponentIdeal_norm]; exact hp
  have hMv' : (Ideal.absNorm (M p'.1) : ℝ) ≤ V := by
    rw [sourcePrimeExponentIdeal_norm]; exact hp'
  have hs := idealFrequency_mixed_separation_norm_cutoff F (M p.1) (M p'.1)
    (sourcePrimeExponentIdeal_ne_bot F S₀ p.1) (sourcePrimeExponentIdeal_ne_bot F S₀ p'.1)
    hβ hβ' hr₀ hn hMv hMv'
  have hb := mixedEmbedding_norm_le_idealModule_trace_coordinates F O top_ne_bot (β - β' + r₀)
  rw [idealModuleTraceCoordinates_add, idealModuleTraceCoordinates_sub,
    show coord r₀ = fun j => (k j : ℝ) from idealModuleTraceIntegerLift_coordinates F O top_ne_bot k] at hb
  have hpow := hs.trans (pow_le_pow_left₀ (norm_nonneg _) hb (Module.finrank ℚ F))
  have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ 1 / (|(NumberField.discr F : ℝ)| * V ^ 2))
    hpow (inv_nonneg.mpr (Nat.cast_nonneg (Module.finrank ℚ F)))
  rw [Real.pow_rpow_inv_natCast
    (mul_nonneg (idealModuleTraceReconstructionConstant_pos F O top_ne_bot).le (norm_nonneg _))
    (Module.finrank_pos : 0 < Module.finrank ℚ F).ne'] at hroot
  unfold idealModuleCoordinateSeparationRadius
  rw [Ideal.absNorm_top, Nat.cast_one, mul_one]
  exact (div_le_iff₀ (idealModuleTraceReconstructionConstant_pos F O top_ne_bot)).mpr
    (by simpa only [mul_comm] using hroot)

end
end ArtinMatthews.SourcePhysical
