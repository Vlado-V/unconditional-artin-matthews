module

public import ArtinMatthews.QuotientUnitChanges
public import ArtinMatthews.ProbeIdealPoissonCRTHelpers
public import ArtinMatthews.ProbeIdealPoissonResidues
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

/-! Exact congruence-kernel reindexing by actual quotient units.
The two weight transformation rules are explicit; no local coefficient
evaluation or phase-normalization identity is assumed. -/
namespace ArtinMatthews.SourceCRTNormalization

open ArtinMatthews.VaryingKummerAnalytic
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R]

theorem quotientUnit_gate_iff (I J : Ideal R) (A H A₀ H₀ : R)
    (C U : (R ⧸ (I * J))ˣ)
    (hH : Ideal.Quotient.mk (I * J) H = (C : R ⧸ (I * J)) * Ideal.Quotient.mk _ H₀)
    (hA : Ideal.Quotient.mk (I * J) A * (U : R ⧸ (I * J)) = (C : R ⧸ (I * J)) * Ideal.Quotient.mk _ A₀)
    (d : R ⧸ I) :
    H - A * Quotient.out ((quotientUnitProjection (Ideal.mul_le_left : I * J ≤ I) U : R ⧸ I) * d) ∈ I ↔
      H₀ - A₀ * Quotient.out d ∈ I := by
  rw [probeIdealPoisson_gate_congr I A H _ _
    (quotientUnit_out_mul_sub_mem (Ideal.mul_le_left : I * J ≤ I) U d)]
  have he := congrArg (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I))
    (quotientUnit_frequency_eq I J A H A₀ H₀ C U hH hA (Quotient.out d))
  rw [map_mul] at he
  change Ideal.Quotient.mk I (H - A * (Quotient.out (U : R ⧸ (I * J)) * Quotient.out d)) =
    (quotientUnitProjection (Ideal.mul_le_left : I * J ≤ I) C : R ⧸ I) *
      Ideal.Quotient.mk I (H₀ - A₀ * Quotient.out d) at he
  rw [← Ideal.Quotient.eq_zero_iff_mem, he, quotientUnit_mul_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

theorem quotientUnit_phase (I J : Ideal R) (A H A₀ H₀ : R) (hAJ : A ∈ J)
    (C U V : (R ⧸ (I * J))ˣ)
    (hH : Ideal.Quotient.mk (I * J) H = (C : R ⧸ (I * J)) * Ideal.Quotient.mk _ H₀)
    (hA : Ideal.Quotient.mk (I * J) A * (U : R ⧸ (I * J)) = (C : R ⧸ (I * J)) * Ideal.Quotient.mk _ A₀)
    (ψ : AddChar (R ⧸ (I * J)) ℂ) (d : R ⧸ I) (v : R ⧸ J)
    (hd : H - A * Quotient.out
      ((quotientUnitProjection (Ideal.mul_le_left : I * J ≤ I) U : R ⧸ I) * d) ∈ I) :
    ψ (Ideal.Quotient.mk _
      ((H - A * Quotient.out ((quotientUnitProjection (Ideal.mul_le_left : I * J ≤ I) U : R ⧸ I) * d)) *
        Quotient.out ((quotientUnitProjection (Ideal.mul_le_right : I * J ≤ J) V : R ⧸ J) * v))) =
      ψ.mulShift ((C * V : (R ⧸ (I * J))ˣ) : R ⧸ (I * J))
        (Ideal.Quotient.mk _ ((H₀ - A₀ * Quotient.out d) * Quotient.out v)) := by
  rw [probeIdealPoisson_phase_congr_le I J (I * J) le_rfl A H _ _ _ _ hAJ
    (quotientUnit_out_mul_sub_mem (Ideal.mul_le_left : I * J ≤ I) U d)
    (quotientUnit_out_mul_sub_mem (Ideal.mul_le_right : I * J ≤ J) V v) hd]
  rw [AddChar.mulShift_apply]
  apply congrArg ψ
  rw [map_mul, quotientUnit_frequency_eq I J A H A₀ H₀ C U hH hA,
    map_mul, Ideal.Quotient.mk_out, map_mul]
  change (C : R ⧸ (I * J)) * _ * ((V : R ⧸ (I * J)) * _) =
    ((C : R ⧸ (I * J)) * (V : R ⧸ (I * J))) * (_ * _)
  ring

theorem quotientCongruenceKernel_unit_change (I J : Ideal R) (A H A₀ H₀ : R)
    (hAJ : A ∈ J) (C U V : (R ⧸ (I * J))ˣ)
    (hH : Ideal.Quotient.mk (I * J) H = (C : R ⧸ (I * J)) * Ideal.Quotient.mk _ H₀)
    (hA : Ideal.Quotient.mk (I * J) A * (U : R ⧸ (I * J)) = (C : R ⧸ (I * J)) * Ideal.Quotient.mk _ A₀)
    (ψ : AddChar (R ⧸ (I * J)) ℂ) (W : R ⧸ I → ℂ) (Z : R ⧸ J → ℂ) (α β : ℂ)
    (hW : ∀ d, W ((quotientUnitProjection (Ideal.mul_le_left : I * J ≤ I) U : R ⧸ I) * d) = α * W d)
    (hZ : ∀ v, Z ((quotientUnitProjection (Ideal.mul_le_right : I * J ≤ J) V : R ⧸ J) * v) = β * Z v) :
    quotientCongruenceKernel I J A H ψ W Z =
      α * β * quotientCongruenceKernel I J A₀ H₀
        (ψ.mulShift ((C * V : (R ⧸ (I * J))ˣ) : R ⧸ (I * J))) W Z := by
  let u := quotientUnitProjection (Ideal.mul_le_left : I * J ≤ I) U
  let v := quotientUnitProjection (Ideal.mul_le_right : I * J ≤ J) V
  let F := fun (d : R ⧸ I) (w : R ⧸ J) =>
    if H - A * Quotient.out d ∈ I then
      W d * Z w * ψ (Ideal.Quotient.mk _ ((H - A * Quotient.out d) * Quotient.out w)) else 0
  let G := fun (d : R ⧸ I) (w : R ⧸ J) =>
    if H₀ - A₀ * Quotient.out d ∈ I then
      W d * Z w * ψ.mulShift ((C * V : (R ⧸ (I * J))ˣ) : R ⧸ (I * J))
        (Ideal.Quotient.mk _ ((H₀ - A₀ * Quotient.out d) * Quotient.out w)) else 0
  have hp (d : R ⧸ I) (w : R ⧸ J) : F (u * d) (v * w) = (α * β) * G d w := by
    dsimp only [F, G]
    have hg := quotientUnit_gate_iff I J A H A₀ H₀ C U hH hA d
    by_cases hd : H₀ - A₀ * Quotient.out d ∈ I
    · rw [ite_eq_left (hg.mpr hd), ite_eq_left hd, hW, hZ,
        quotientUnit_phase I J A H A₀ H₀ hAJ C U V hH hA ψ d w (hg.mpr hd)]
      ring
    · rw [ite_eq_right (fun h => hd (hg.mp h)), ite_eq_right hd, mul_zero]
  change (∑' d, ∑' w, F d w) = (α * β) * ∑' d, ∑' w, G d w
  calc
    _ = ∑' d, ∑' w, F (u * d) (v * w) := by
      rw [← u.mulLeft.tsum_eq (fun d => ∑' w, F d w)]
      apply tsum_congr
      intro d
      exact (v.mulLeft.tsum_eq (fun w => F (u * d) w)).symm
    _ = ∑' d, ∑' w, (α * β) * G d w := by
      apply tsum_congr
      intro d
      exact tsum_congr (hp d)
    _ = _ := by simp only [tsum_mul_left]

end
end ArtinMatthews.SourceCRTNormalization
