module

public import ArtinMatthews.SourceKPTameCyclicUpperAverage
public import ArtinMatthews.SourceJacquetAdditiveTranslation
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.StandardLocalFourier
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.Local.CompactCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! The Haar integral of the actual upper-root average on both
Bruhat cells. On the closed cell and distant open cosets, character
orthogonality kills the constant evaluation. Inside the ball, it
is exactly the finite Jacquet integral with its Borel multiplier. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical QuadraticWeil MeasureTheory
open OAI.RepresentationTheory.Weil.Local
open scoped NumberField SourcePhysical Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "C₀" => sourceKPTameSphericalCyclicSpace K hζ S₀ P
local notation "P₀" => SourceFiniteKPProjectiveBorel K hζ P.val
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "τ₀" => sourceKPTameBorelRepresentation K hζ P.val h₆ π₀ hπ₀
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "ν₀" => sourceLocalValuation K P.val
local notation "B" => sourceLocalBall K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "E₀" => sourceKPTameCyclicUpperIntegrand K hζ S₀ P
local notation "I₀" => sourceKPTameJacquetInducedIntegrand K hζ S₀ P

theorem sourceJacquetBall_negative_character_integral_zero (hP : P.val ∉ traceBadPlaces K)
    (R : ℕ) (hR : 1 ≤ R) : (∫ t in B (R : ℤ), ψ₀ (-t) ∂μ₀) = 0 := by
  let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
  let χ := (ψ₀).mulShift (-1)
  have hI := CompactCharacter.Construction.integral_character_subgroup μ₀
    (sourceLocalOpenBall K P.val (R : ℤ)) χ
  change (∫ t in B (R : ℤ), ψ₀ ((-1 : L) * t) ∂μ₀) =
    if ∀ t ∈ B (R : ℤ), ψ₀ ((-1 : L) * t) = 1 then (Measure.real μ₀ (B (R : ℤ)) : ℂ) else 0 at hI
  simp only [neg_one_mul] at hI
  obtain ⟨t, ht, hψ⟩ := sourceLocalCharacter_next_ball_nontrivial K P.val
  rw [(sourceDifferentExponent_eq_zero_iff K P.val).mpr hP, Nat.cast_zero, zero_add] at ht
  have htR : t ∈ B (R : ℤ) := (show ν₀ t ≤ WithZero.exp (1 : ℤ) from ht).trans
    (WithZero.exp_le_exp.mpr (by omega))
  have hn : ¬∀ t ∈ B (R : ℤ), ψ₀ (-t) = 1 := by
    intro h
    apply hψ
    have he := h t htR
    rw [AddChar.map_neg_eq_inv] at he
    simpa only [inv_inv, inv_one] using congrArg Inv.inv he
  rwa [ite_eq_right hn] at hI

theorem sourceKPTameCyclicUpperIntegral_closed (f : C₀) (b : P₀)
    (hP : P.val ∉ traceBadPlaces K) (R : ℕ) (hR : 1 ≤ R) :
    (∫ t in B (R : ℤ), E₀ f b.val t ∂μ₀) = 0 := by
  have hn (t : L) : f.val.val (n₀ t) = f.val.val 1 := by
    have h := f.val.property (sourceFiniteKPProjectiveBorelUpper K hζ P.val t) 1
    rwa [mul_one, sourceFiniteKPProjectiveBorelUpper_val, sourceKPTameBorelRepresentation_upper] at h
  have hb (t : L) : f.val.val (b.val * n₀ t) = f.val.val b.val := by
    calc
      _ = τ₀ b (f.val.val (n₀ t)) := f.val.property b (n₀ t)
      _ = τ₀ b (f.val.val 1) := congrArg (τ₀ b) (hn t)
      _ = _ := by simpa only [mul_one] using (f.val.property b 1).symm
  have he : E₀ f b.val = fun t => ψ₀ (-t) • f.val.val b.val := by
    funext t
    exact congrArg (ψ₀ (-t) • ·) (hb t)
  rw [he, integral_smul_const, sourceJacquetBall_negative_character_integral_zero K S₀ P hP R hR, zero_smul]

theorem sourceKPTameCyclicUpperIntegral_open_outside (f : C₀) (b : P₀) (x : L)
    (hP : P.val ∉ traceBadPlaces K) (R : ℕ) (hR : 1 ≤ R)
    (hcusp : ∀ t ∈ B (R : ℤ), f.val.val (w₀ * n₀ (x + t)) = f.val.val (w₀ * n₀ x)) :
    (∫ t in B (R : ℤ), E₀ f (b.val * w₀ * n₀ x) t ∂μ₀) = 0 := by
  have he : Set.EqOn (E₀ f (b.val * w₀ * n₀ x))
      (fun t => ψ₀ (-t) • τ₀ b (f.val.val (w₀ * n₀ x))) (B (R : ℤ)) := by
    intro t ht
    change ψ₀ (-t) • f.val.val ((b.val * w₀ * n₀ x) * n₀ t) = _
    rw [mul_assoc (b.val * w₀), sourceFiniteKP2ProjectiveLift_upper_add, mul_assoc b.val,
      f.val.property b, hcusp t ht]
  rw [setIntegral_congr_fun (sourceLocalBall_isOpen K P.val _).measurableSet he,
    integral_smul_const, sourceJacquetBall_negative_character_integral_zero K S₀ P hP R hR, zero_smul]

theorem sourceKPTameCyclicUpperIntegral_open_inside (f : C₀) (b : P₀) (x : L) (R : ℕ)
    (hx : x ∈ B (R : ℤ)) (hi : IntegrableOn (I₀ f.val) (B (R : ℤ)) μ₀) :
    (∫ t in B (R : ℤ), E₀ f (b.val * w₀ * n₀ x) t ∂μ₀) =
      τ₀ b (ψ₀ x • sourceKPTameJacquetInducedTruncation K hζ S₀ P f.val R) := by
  let τ : (ZMod 3 → ℂ) →L[ℂ] (ZMod 3 → ℂ) := LinearMap.toContinuousLinearMap (τ₀ b)
  have hτ (v : ZMod 3 → ℂ) : τ v = τ₀ b v := rfl
  have he : E₀ f (b.val * w₀ * n₀ x) = fun t => τ (ψ₀ x • I₀ f.val (t + x)) := by
    funext t
    change ψ₀ (-t) • f.val.val ((b.val * w₀ * n₀ x) * n₀ t) = τ (ψ₀ x • I₀ f.val (t + x))
    rw [mul_assoc (b.val * w₀), sourceFiniteKP2ProjectiveLift_upper_add, mul_assoc b.val,
      f.val.property b, hτ, ← map_smul]
    change τ₀ b (ψ₀ (-t) • f.val.val (w₀ * n₀ (x + t))) =
      τ₀ b (ψ₀ x • (ψ₀ (-(t + x)) • f.val.val (w₀ * n₀ (t + x))))
    rw [smul_smul, ← AddChar.map_add_eq_mul, show x + -(t + x) = -t by abel, add_comm t x]
  have hj : IntegrableOn (fun t => ψ₀ x • I₀ f.val (t + x)) (B (R : ℤ)) μ₀ :=
    ((sourceJacquetBall_translate_integrable_iff K P.val (R : ℤ) x hx (I₀ f.val)).mpr hi).smul (ψ₀ x)
  rw [he]
  change (∫ t in B (R : ℤ), τ (ψ₀ x • I₀ f.val (t + x)) ∂μ₀) = _
  rw [τ.integral_comp_comm hj, integral_smul, sourceJacquetBall_translate_integral K P.val (R : ℤ) x hx,
    hτ, sourceKPTameJacquetInducedTruncation]


end
end ArtinMatthews
