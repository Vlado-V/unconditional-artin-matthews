module

public import ArtinMatthews.StandardAdelicCharacter
public import ArtinMatthews.StandardAdelicCharacterData
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine negative trace character at a nonzero rational
frequency. Multiplication by the rational unit transports the actual
standard character, including its nontriviality. -/

namespace ArtinMatthews
open NumberField StandardAdelic
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPTraceJacquetCharacter (m : Kˣ) (y : 𝔸[K]) : ℂ :=
  star (StandardAdelic.character K (algebraMap K 𝔸[K] (m : K) * y))

theorem sourceKPTraceJacquetCharacter_add (m : Kˣ) (y z : 𝔸[K]) :
    sourceKPTraceJacquetCharacter K m (y+z) =
      sourceKPTraceJacquetCharacter K m y * sourceKPTraceJacquetCharacter K m z := by
  simp only [sourceKPTraceJacquetCharacter, mul_add, AddChar.map_add_eq_mul, star_mul']

theorem sourceKPTraceJacquetCharacter_continuous (m : Kˣ) :
    Continuous (sourceKPTraceJacquetCharacter K m) :=
  continuous_star.comp ((character_continuous K).comp (continuous_const.mul continuous_id))

theorem sourceKPTraceJacquetCharacter_norm (m : Kˣ) (y : 𝔸[K]) :
    ‖sourceKPTraceJacquetCharacter K m y‖ = 1 := by
  rw [sourceKPTraceJacquetCharacter, norm_star, character_unitary]

theorem sourceKPTraceJacquetCharacter_principal (m : Kˣ) (x : K) :
    sourceKPTraceJacquetCharacter K m (algebraMap K 𝔸[K] x) = 1 := by
  rw [sourceKPTraceJacquetCharacter, ← map_mul, character_principal, star_one]

theorem sourceKPTraceJacquetCharacter_rational_add (m : Kˣ) (x : K) (y : 𝔸[K]) :
    sourceKPTraceJacquetCharacter K m (y+algebraMap K 𝔸[K] x) =
      sourceKPTraceJacquetCharacter K m y := by
  rw [sourceKPTraceJacquetCharacter_add, sourceKPTraceJacquetCharacter_principal, mul_one]

theorem sourceKPTraceJacquetCharacter_nontrivial (m : Kˣ) :
    ∃ y : 𝔸[K], sourceKPTraceJacquetCharacter K m y ≠ 1 := by
  obtain ⟨z,hz⟩ := character_nontrivial K
  have hm : algebraMap K 𝔸[K] (m : K) * algebraMap K 𝔸[K] ((m⁻¹ : Kˣ) : K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine ⟨algebraMap K 𝔸[K] ((m⁻¹ : Kˣ) : K) * z, ?_⟩
  rw [sourceKPTraceJacquetCharacter, ← mul_assoc, hm, one_mul]
  intro h
  apply hz
  apply star_injective
  simpa only [star_one] using h

end
end ArtinMatthews
