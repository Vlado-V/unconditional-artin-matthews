module

public import ArtinMatthews.SourceReflectionFrozenWeights
public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourceReflectionDyadicScale
public import ArtinMatthews.SourceReflectionIdealCutoffs
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

/-! The exterior-ideal form of the Section 04 expansion and its exact
quadratic symbol. The automorphic expansion and the quadratic sieve
remain explicit inputs to the deterministic moment proof. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical BigOperators ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceReflectionQuadraticSymbol (d c : E) : ℂ :=
  reflectionExponentResidueValue F hζ S₀ d (sourcePrimeExponentGenerator F hζ S₀ c) ^ 3

theorem sourceReflectionQuadraticSymbol_norm_le_one (d c : E) :
    ‖sourceReflectionQuadraticSymbol F S₀ hζ d c‖ ≤ 1 := by
  rw [sourceReflectionQuadraticSymbol, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (reflectionExponentResidueValue_norm_le_one F hζ S₀ _ _)

def SourceReflectionQuadraticSieve : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ ∀ D C : ℝ, 1 ≤ D → 1 ≤ C →
    ∀ (rows cols : Finset E),
      (∀ d ∈ rows, sourceReflectionIsSquarefree d ∧ (q d : ℝ) ≤ D) →
      (∀ c ∈ cols, sourceReflectionIsSquarefree c ∧ (q c : ℝ) ≤ C) →
      ∀ a : cols → ℂ,
        (∑ d : rows, ‖∑ c : cols, sourceReflectionQuadraticSymbol F S₀ hζ d.val c.val * a c‖ ^ 2) ≤
          B * (D + C) * (D * C) ^ ε * ∑ c : cols, ‖a c‖ ^ 2

/-- Data for one fixed row-unit class. The finite type U contains the
frequency-unit class and the two allowed-class slices. The row and
column factors may include their separate coprimality indicators. -/
structure SourceReflectionExpansionData (U : Type) where
  scalar : E → Finset Prime → E → E → U → ℂ
  row : E → Finset Prime → E → E → U → E → ℂ
  column : E → Finset Prime → E → E → U → E → ℂ
  profile : E → Finset Prime → E → E → U → ℝ → ℂ
  scalar_bound : ∀ h f a n u, ‖scalar h f a n u‖ ≤ sourceReflectionFrozenWeight F S₀ f a
  row_bound : ∀ h f a n u d, ‖row h f a n u d‖ ≤ 1
  column_bound : ∀ h f a n u c, ‖column h f a n u c‖ ≤ 1
  profile_smooth : ∀ h f a n u, ContDiff ℝ ∞ (fun x : ℝ => profile h f a n u (Real.exp x))
  profile_derivative : ∃ α : ℝ, 0 ≤ α ∧ ∀ A : ℝ, 0 < A →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h f a n u k, k ≤ 2 → ∀ x : ℝ,
      ‖iteratedFDeriv ℝ k (fun y : ℝ => profile h f a n u (Real.exp y)) x‖ ≤
        M * min (Real.exp (α * x)) (Real.exp (-A * x))

def sourceReflectionTermLength (a n c : E) : ℝ := (q a : ℝ) * q c * (q n : ℝ) ^ 3

def sourceReflectionTermScale (Z : ℝ) (f : Finset Prime) (d : E) : ℝ :=
  (q d : ℝ) ^ 2 * (q (sourceReflectionActiveExponents F S₀ f) : ℝ) ^ 2 / Z

theorem sourceReflectionTermLength_one_le (a n c : E) :
    1 ≤ sourceReflectionTermLength F S₀ a n c := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le (sourceReflection_norm_one_le F S₀ a)
      (sourceReflection_norm_one_le F S₀ c)
  · exact one_le_pow₀ (sourceReflection_norm_one_le F S₀ n)

theorem sourceReflectionTermScale_pos {Z : ℝ} (hZ : 0 < Z) (f : Finset Prime) (d : E) :
    0 < sourceReflectionTermScale F S₀ Z f d := by
  have hd := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ d)
  have hf := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ (sourceReflectionActiveExponents F S₀ f))
  unfold sourceReflectionTermScale
  positivity

theorem sourceReflectionTermScale_le {Z P D : ℝ} (hZ : 0 < Z) {h d : E}
    (hh : sourceReflectionIsPowerful h) (hhP : (q h : ℝ) ≤ 2 * P) (hdD : (q d : ℝ) ≤ 2 * D)
    {f : Finset Prime} (hf : f ∈ sourceReflectionActiveChoices F S₀ h) :
    sourceReflectionTermScale F S₀ Z f d ≤ sourceReflectionLength Z P D :=
  sourceReflectionRowScale_le hZ (Nat.cast_nonneg _) hdD
    ((sourceReflectionActiveChoice_sq_le F S₀ hh hf).trans hhP)

def sourceReflectionColumnCoefficient {U : Type} (A : SourceReflectionExpansionData F S₀ U)
    (h : E) (f : Finset Prime) (a n : E) (u : U) (c : E) : ℂ :=
  A.column h f a n u c / (Real.sqrt (q c : ℝ) : ℂ)

theorem sourceReflectionColumnCoefficient_norm_sq_le {U : Type}
    (A : SourceReflectionExpansionData F S₀ U) (h : E) (f : Finset Prime)
    (a n : E) (u : U) (c : E) :
    ‖sourceReflectionColumnCoefficient F S₀ A h f a n u c‖ ^ 2 ≤ (q c : ℝ)⁻¹ := by
  unfold sourceReflectionColumnCoefficient
  have hc : (0 : ℝ) < q c := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ c)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt hc.le, ← one_div]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (A.column_bound h f a n u c)) hc.le

def sourceReflectionExpansionTerm {U : Type} (A : SourceReflectionExpansionData F S₀ U)
    (Z : ℝ) (h d : E) (f : Finset Prime) (a n c : E) (u : U) : ℂ :=
  (A.scalar h f a n u / (q n : ℂ)) *
    (A.row h f a n u d * sourceReflectionQuadraticSymbol F S₀ hζ d c *
      sourceReflectionColumnCoefficient F S₀ A h f a n u c *
      A.profile h f a n u (sourceReflectionTermLength F S₀ a n c /
        sourceReflectionTermScale F S₀ Z f d))

theorem sourceReflectionTermLength_div_scale {Z : ℝ} (hZ : 0 < Z)
    (f : Finset Prime) (a n c d : E) :
    sourceReflectionTermLength F S₀ a n c / sourceReflectionTermScale F S₀ Z f d =
      (Z * (q a : ℝ) * (q n : ℝ) ^ 3 / (q (sourceReflectionActiveExponents F S₀ f) : ℝ) ^ 2) *
        q c / (q d : ℝ) ^ 2 := by
  have hf : (0 : ℝ) < q (sourceReflectionActiveExponents F S₀ f) :=
    zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ _)
  have hd : (0 : ℝ) < q d := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ d)
  unfold sourceReflectionTermLength sourceReflectionTermScale
  field_simp

end
end ArtinMatthews.SourceEulerAssembly
