module

public import ArtinMatthews.SourceKPTraceJacquetLocalOrdinary
public import ArtinMatthews.SourceJacquetAdditiveTranslation
public import ArtinMatthews.SourceJacquetDeepFrequency
public import ArtinMatthews.SourceKPCoupledTameShellMeasure
public import ArtinMatthews.SourceKPTameIntertwiningIntegral
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The ordinary nonzero-frequency integral has an exact finite shell
cutoff. The unit-ball term and the cutoff come from the actual
conductor-zero character and the residue-weight cancellation. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical QuadraticWeil
open VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "B₀" => sourceLocalBall K P.val
local notation "shell₀" => sourceJacquetValuationShell K P.val

theorem sourceKPTraceJacquetLocalPhase_integer_integral (hP : P.val ∉ traceBadPlaces K) (m : L) :
    (∫ x in B₀ 0, ψ₀ (-(m*x)) ∂μ₀) = if ν₀ m ≤ 1 then 1 else 0 := by
  let f : L → ℂ := fun x => ψ₀ (-(m*x))
  have hB := (sourceLocalBall_isCompact K P.val 0).measurableSet
  by_cases hm : ν₀ m ≤ 1
  · rw [ite_eq_left hm]
    have he (x : L) (hx : x ∈ B₀ 0) : f x = 1 := by
      apply localFiniteCharacter_integral
      apply (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P.val).mpr
      have hx' : ν₀ x ≤ 1 := by
        change ν₀ x ≤ WithZero.exp (0 : ℤ) at hx
        simpa only [WithZero.exp_zero] using hx
      change ν₀ (-(m*x)) ≤ 1
      rw [Valuation.map_neg, map_mul]
      exact (mul_le_mul' hm hx').trans_eq (one_mul _)
    change (∫ x in B₀ 0, f x ∂μ₀) = 1
    rw [setIntegral_congr_fun hB he, integral_const, Measure.real, Measure.restrict_apply_univ,
      ← Measure.real, sourceKPCoupledJacquetBall_mass K P.val, one_smul]
  · rw [ite_eq_right hm]
    have hn : -m ∉ P.val.adicCompletionIntegers K := by
      intro h
      apply hm
      have hv := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P.val).mp h
      change ν₀ (-m) ≤ 1 at hv
      simpa only [Valuation.map_neg] using hv
    have hno := mt (adicConductorZero_dual K P.val ψ₀
      (localFiniteCharacter_conductorZero K P.val hP) (-m)).mp hn
    push Not at hno
    obtain ⟨a,ha,hψ⟩ := hno
    have haB : a ∈ B₀ 0 := by
      change ν₀ a ≤ WithZero.exp (0 : ℤ)
      rw [WithZero.exp_zero]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P.val).mp ha
    have hψ' : f a ≠ 1 := by
      dsimp only [f]
      rw [← neg_mul]
      exact hψ
    have ht := sourceJacquetBall_translate_integral K P.val 0 a haB f
    have he (x : L) : f (x+a) = f x * f a := by
      dsimp only [f]
      rw [mul_add, neg_add, AddChar.map_add_eq_mul]
    simp_rw [he] at ht
    rw [integral_mul_const] at ht
    change (∫ x in B₀ 0, f x ∂μ₀) = 0
    by_contra h
    exact hψ' (mul_left_cancel₀ h (ht.trans (mul_one _).symm))

theorem sourceKPTraceJacquetLocalOrdinary_integer_ball (hP : P.val ∉ traceBadPlaces K) (s : ℂ) (m : L) :
    (∫ x in B₀ 0, sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m x ∂μ₀) =
      (if ν₀ m ≤ 1 then (1 : ℂ) else 0) • sourceJacquetBasis 0 := by
  have he (x : L) (hx : x ∈ B₀ 0) :
      sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m x =
        ψ₀ (-(m*x)) • sourceJacquetBasis 0 := by
    rw [sourceKPTraceJacquetLocalOrdinaryIntegrand,
      sourceKPTameIntertwiningIntegrand_on_zero K hζ S₀ P s x hx]
  rw [setIntegral_congr_fun (sourceLocalBall_isCompact K P.val 0).measurableSet he,
    integral_smul_const, sourceKPTraceJacquetLocalPhase_integer_integral K S₀ P hP m]

def sourceKPTraceJacquetLocalRadius (p : HeightOneSpectrum (𝓞 K)) (m : (p.adicCompletion K)ˣ) : ℕ :=
  (sourceKPValuationOrder (sourceKPFiniteVal K p) m + 1).toNat

theorem sourceKPTraceJacquetLocalShellFrequency_valuation (m : Lˣ) (l : ℕ) :
    ν₀ ((m : L) * ((π₀^(-(l : ℤ)) : Lˣ) : L)) =
      WithZero.exp ((l : ℤ)-sourceKPValuationOrder ν₀ m) := by
  have ht : ν₀ (((π₀^(-(l : ℤ)) : Lˣ) : L)) = WithZero.exp (l : ℤ) := by
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀, neg_neg]
  rw [map_mul, sourceKPValuationOrder_spec ν₀ m, ht, ← WithZero.exp_add]
  congr 1
  ring

theorem sourceKPTraceJacquetLocalOrdinary_shell_zero (hP : P.val ∉ traceBadPlaces K)
    (s : ℂ) (m : Lˣ) (l : ℕ) (hl : sourceKPTraceJacquetLocalRadius K P.val m < l) :
    (∫ x in shell₀ (l : ℤ), sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s (m : L) x ∂μ₀) = 0 := by
  let t := (m : L) * ((π₀^(-(l : ℤ)) : Lˣ) : L)
  have hv : WithZero.exp (2 : ℤ) ≤ ν₀ t := by
    change WithZero.exp (2 : ℤ) ≤ ν₀ ((m : L) * ((π₀^(-(l : ℤ)) : Lˣ) : L))
    rw [sourceKPTraceJacquetLocalShellFrequency_valuation K hζ S₀ P m l, WithZero.exp_le_exp]
    unfold sourceKPTraceJacquetLocalRadius at hl
    omega
  rw [sourceKPTraceJacquetLocalOrdinary_shell K hζ S₀ P hP s (m : L) l,
    sourceJacquetShellIntegral_deep_frequency K P.val
      (sourceJacquetShellCharacter K P.val χ₀ l) (π₀ : L) t hπ₀ hv hP, mul_zero, zero_smul]

end
end ArtinMatthews
