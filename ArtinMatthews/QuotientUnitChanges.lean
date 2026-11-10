module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Ideal.Quotient.Defs
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual changes by units of a larger finite quotient. Representatives
need only be units modulo the ideal, not units in the ambient ring. -/
namespace ArtinMatthews.SourceCRTNormalization

open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R]

def quotientUnitProjection {I M : Ideal R} (h : M ≤ I) (u : (R ⧸ M)ˣ) : (R ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.factor h).toMonoidHom u

theorem quotientUnitProjection_val {I M : Ideal R} (h : M ≤ I) (u : (R ⧸ M)ˣ) :
    (quotientUnitProjection h u : R ⧸ I) =
      Ideal.Quotient.mk I (Quotient.out (u : R ⧸ M)) := by
  change Ideal.Quotient.factor h (u : R ⧸ M) = _
  conv_lhs => rw [← Ideal.Quotient.mk_out (u : R ⧸ M)]
  rfl

theorem quotientUnit_out_mul_sub_mem {I M : Ideal R} (h : M ≤ I) (u : (R ⧸ M)ˣ)
    (x : R ⧸ I) :
    Quotient.out ((quotientUnitProjection h u : R ⧸ I) * x) -
      Quotient.out (u : R ⧸ M) * Quotient.out x ∈ I := by
  apply Ideal.Quotient.eq.mp
  rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
    ← quotientUnitProjection_val h u]

theorem quotientUnit_mul_eq_zero_iff {A : Type*} [MonoidWithZero A] (u : Aˣ) (x : A) :
    (u : A) * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply u.mulLeft.injective
    simpa only [Units.mulLeft_apply, mul_zero] using h
  · intro h
    rw [h, mul_zero]

def quotientCongruenceKernel (I J : Ideal R) (A H : R)
    (ψ : AddChar (R ⧸ (I * J)) ℂ) (W : R ⧸ I → ℂ) (Z : R ⧸ J → ℂ) : ℂ :=
  ∑' d : R ⧸ I, ∑' v : R ⧸ J,
    if H - A * Quotient.out d ∈ I then
      W d * Z v * ψ (Ideal.Quotient.mk _ ((H - A * Quotient.out d) * Quotient.out v))
    else 0

theorem quotientUnit_frequency_eq (I J : Ideal R) (A H A₀ H₀ : R)
    (C U : (R ⧸ (I * J))ˣ)
    (hH : Ideal.Quotient.mk (I * J) H = (C : R ⧸ (I * J)) * Ideal.Quotient.mk _ H₀)
    (hA : Ideal.Quotient.mk (I * J) A * (U : R ⧸ (I * J)) = (C : R ⧸ (I * J)) * Ideal.Quotient.mk _ A₀) (d : R) :
    Ideal.Quotient.mk (I * J) (H - A * (Quotient.out (U : R ⧸ (I * J)) * d)) =
      (C : R ⧸ (I * J)) * Ideal.Quotient.mk _ (H₀ - A₀ * d) := by
  rw [map_sub, map_mul, map_mul, Ideal.Quotient.mk_out, hH, ← mul_assoc, hA, map_sub, map_mul]
  ring

end
end ArtinMatthews.SourceCRTNormalization
