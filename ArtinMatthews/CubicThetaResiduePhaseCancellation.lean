module

public import ArtinMatthews.CubicThetaResidueNorm
public import ArtinMatthews.CubicThetaInflatedCancellation
public import ArtinMatthews.CubicThetaResidueReduction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Cancellation of the actual finite two-coordinate rational phase sum. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

local notation "EO" => HeckeFamily.O

def cubicThetaFinCastEquiv (M : ℕ) [NeZero M] : Fin M ≃ ZMod M where
  toFun a := (a : ℕ)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv a := Fin.ext (ZMod.val_natCast_of_lt a.isLt)
  right_inv z := ZMod.natCast_zmod_val z

def cubicThetaFiniteCoordinates (M : ℕ) [NeZero M] :
    (Fin M × Fin M) ≃ CubicThetaResidue M :=
  (Equiv.prodCongr (cubicThetaFinCastEquiv M) (cubicThetaFinCastEquiv M)).trans
    (cubicThetaCoordinateEquiv M)

@[simp] theorem cubicThetaFiniteCoordinates_apply (M : ℕ) [NeZero M]
    (r : Fin M × Fin M) :
    cubicThetaFiniteCoordinates M r =
      Ideal.Quotient.mk (cubicThetaRationalModulus M)
        (HeckeFamily.coordinateElement r.1 r.2) := by
  change cubicThetaCoordinateEquiv M ((r.1 : ℕ), (r.2 : ℕ)) = _
  simpa only [Int.cast_natCast] using
    cubicThetaCoordinateEquiv_intCast M (r.1 : ℤ) (r.2 : ℤ)

/-- This arithmetic form is independent of the analytic cusp limit. It
uses the proved lifting of norm-one units to an enlarged modulus. -/
theorem cubicThetaResidue_phase_sum_eq_zero (A : ℤ) (M : ℕ) [NeZero M]
    (hdiv : 9 * A ∣ (M : ℤ))
    (χ : MulChar (EO ⧸ cubicNumeratorHeckeModulus A) ℂ)
    (hχσ : ∀ u : (EO ⧸ cubicNumeratorHeckeModulus A)ˣ,
      χ (cubicNumeratorResidueConjugation A u) = (χ u)⁻¹)
    (hcubic : ∀ u : (EO ⧸ cubicNumeratorHeckeModulus A)ˣ, χ u ^ 3 = 1)
    (hne : χ ≠ 1) (a : ℤ) :
    (∑ r : Fin M × Fin M,
      χ (Ideal.Quotient.mk (cubicNumeratorHeckeModulus A)
        (HeckeFamily.coordinateElement r.1 r.2)) *
          eisensteinRationalPhase a M ((r.1 : ℤ), (r.2 : ℤ))) = 0 := by
  let f := cubicThetaResidueReduction A M hdiv
  let e := cubicThetaFiniteCoordinates M
  let F := cubicThetaResidueNormPhase a M
  have hsum := anticyclotomic_cubic_inflated_sum_norm_eq_zero
    f (cubicThetaResidueReduction_surjective A M hdiv)
    (cubicThetaResidueConjugation M) (cubicNumeratorResidueConjugation A)
    (cubicThetaResidueConjugation_involutive M)
    (cubicThetaResidueReduction_conjugate A M hdiv) χ hχσ hcubic hne F
  calc
    _ = ∑ r : Fin M × Fin M,
        χ (f (e r)) * F (e r * cubicThetaResidueConjugation M (e r)) := by
      apply Finset.sum_congr rfl
      intro r _
      have hp := cubicThetaResidueNormPhase_coordinates a M (r.1 : ℤ) (r.2 : ℤ)
      simp only [Int.cast_natCast] at hp
      change F (e r * cubicThetaResidueConjugation M (e r)) = _ at hp
      rw [← hp]
      change _ = χ (cubicThetaResidueReduction A M hdiv
        (cubicThetaFiniteCoordinates M r)) * _
      rw [cubicThetaFiniteCoordinates_apply, cubicThetaResidueReduction_mk]
    _ = ∑ x : CubicThetaResidue M, χ (f x) * F (x * cubicThetaResidueConjugation M x) :=
      e.bijective.sum_comp (fun x : CubicThetaResidue M =>
        χ (f x) * F (x * cubicThetaResidueConjugation M x))
    _ = 0 := hsum

end ArtinMatthews
