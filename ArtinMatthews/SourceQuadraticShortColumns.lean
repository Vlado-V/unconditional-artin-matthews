module

public import ArtinMatthews.SourceQuadraticCommonGram
public import OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourceQuadraticCommonIdeal
public import ArtinMatthews.SourceQuadraticHeckeSymbols
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
public import OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound


set_option backward.privateInPublic true
@[expose] public section

/-! Stripping a common divisor embeds the remaining columns into the
actual shorter B2 matrix, with the original smoothed row weight. -/

namespace ArtinMatthews.SourceEulerAssembly
noncomputable section
open NumberField IsDedekindDomain
open OAI.FiniteSieveOperator
open scoped NumberField Classical BigOperators

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

theorem sourceQuadraticSymbol_add_right (d b c : E) : χ d (b + c) = χ d b * χ d c := by
  have hm := sourceReflectionExponentResidueValue_mul F S₀ hζ d
    (sourcePrimeExponentGenerator F hζ S₀ b) (sourcePrimeExponentGenerator F hζ S₀ c)
  unfold sourceReflectionQuadraticSymbol
  rw [sourcePrimeExponentGenerator_add]
  exact (congrArg (fun z : ℂ => z ^ 3) hm).trans (mul_pow _ _ _)

def sourceQuadraticB2Matrix (rows : Finset E) (w : E → ℝ) (N : ℝ) :
    Matrix rows (sourceQuadraticB2Columns F S₀ N) ℂ :=
  fun d b => (Real.sqrt (w d.val) : ℂ) * χ d.val b.val

def sourceQuadraticB2Norm (rows : Finset E) (w : E → ℝ) (N : ℝ) : ℝ :=
  ‖operator (sourceQuadraticB2Matrix F S₀ hζ rows w N)‖ ^ 2

theorem sourceQuadraticB2Norm_nonneg (rows : Finset E) (w : E → ℝ) (N : ℝ) :
    0 ≤ sourceQuadraticB2Norm F S₀ hζ rows w N := sq_nonneg _

def sourceQuadraticDivisibleColumns (cols : Finset E) (g : E) : Finset E :=
  cols.filter (fun b => g ≤ b)

theorem sourceQuadratic_mem_divisibleColumns (cols : Finset E) (g b : E) :
    b ∈ sourceQuadraticDivisibleColumns F S₀ cols g ↔ b ∈ cols ∧ g ≤ b := by
  rw [sourceQuadraticDivisibleColumns, Finset.mem_filter]

def sourceQuadraticShortMatrix (rows cols : Finset E) (w : E → ℝ) (g : E) :
    Matrix rows (sourceQuadraticDivisibleColumns F S₀ cols g) ℂ :=
  fun d b => (Real.sqrt (w d.val) : ℂ) * χ d.val (b.val - g)

theorem sourceQuadraticShortMatrix_norm_le (rows cols : Finset E) (w : E → ℝ)
    (g : E) {N G : ℝ} (hN : 0 ≤ N) (hG : 0 < G) (hg : G ≤ (q g : ℝ))
    (hcols : ∀ b ∈ cols, (q b : ℝ) ≤ N ∧ sourceReflectionIsSquarefree b) :
    ‖operator (sourceQuadraticShortMatrix F S₀ hζ rows cols w g)‖ ^ 2 ≤
      sourceQuadraticB2Norm F S₀ hζ rows w (N / G) := by
  let D := sourceQuadraticDivisibleColumns F S₀ cols g
  let C := sourceQuadraticB2Columns F S₀ (N / G)
  have hD (b : D) : b.val ∈ cols ∧ g ≤ b.val :=
    (sourceQuadratic_mem_divisibleColumns F S₀ cols g b.val).mp b.property
  have hshort (b : D) : b.val - g ∈ C := by
    apply (sourceQuadratic_mem_B2Columns F S₀ (div_nonneg hN hG.le) _).mpr
    obtain ⟨hN', hsf⟩ := hcols b.val (hD b).1
    refine ⟨(le_div_iff₀ hG).mpr ?_, sourceQuadraticExteriorQuotient_squarefree F S₀ _ _ hsf⟩
    calc
      (q (b.val - g) : ℝ) * G ≤ (q (b.val - g) : ℝ) * q g :=
        mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)
      _ = q b.val := by
        rw [mul_comm]
        exact_mod_cast sourceQuadraticExteriorQuotient_norm F S₀ b.val g (hD b).2
      _ ≤ N := hN'
  let f (b : D) : C := ⟨b.val - g, hshort b⟩
  have hf : Function.Injective f := by
    intro b c h
    have he : b.val - g = c.val - g := congrArg Subtype.val h
    apply Subtype.ext
    calc
      b.val = g + (b.val - g) := (add_tsub_cancel_of_le (hD b).2).symm
      _ = g + (c.val - g) := congrArg (g + ·) he
      _ = c.val := add_tsub_cancel_of_le (hD c).2
  have hh := OAI.FiniteSieveRestriction.submatrix_norm_le
    (id : rows → rows) Function.injective_id f hf (sourceQuadraticB2Matrix F S₀ hζ rows w (N / G))
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

theorem sourceQuadratic_scaled_row_sq (cols : Finset E) (w : ℝ) (hw : 0 ≤ w)
    (d : E) (a : cols → ℂ) :
    ‖∑ b : cols, (Real.sqrt w : ℂ) * χ d b.val * a b‖ ^ 2 =
      w * ‖∑ b : cols, χ d b.val * a b‖ ^ 2 := by
  have he : (∑ b : cols, (Real.sqrt w : ℂ) * χ d b.val * a b) =
      (Real.sqrt w : ℂ) * ∑ b : cols, χ d b.val * a b := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [he, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hw]

end
end ArtinMatthews.SourceEulerAssembly
