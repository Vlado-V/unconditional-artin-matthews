module

public import ArtinMatthews.PositiveDensityCubicTraceSum
public import ArtinMatthews.CubicThetaActualCuspFormBase
public import ArtinMatthews.CubicThetaActualCuspFormConstructed
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

/-! The actual nontrivial Frobenius trace statistic is the same shifted
giant-prime statistic of the native weight-one cusp coefficients. -/

noncomputable section
namespace ArtinMatthews

open Filter UpperHalfPlane
open OAI OAI.SevenEighths
open scoped MatrixGroups BigOperators Topology

def giantCubicCuspPrimeTest {A : ℤ}
    (f : CuspForm (cubicThetaKernel (cubicNumeratorThetaLevel A)) 1)
    (twist : ℕ → ℂ) (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x,
    (giantSieveWeight Φ x p : ℂ) * twist p *
      (((giantPrimeFactors (p - 1) x ε).card : ℝ) : ℂ) * (qExpansion 1 f).coeff p

theorem giantCubicTracePrimeTest_has_actual_cuspForm {S : Finset ℤ}
    (hS : AdmissibleBases S)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ)
    (hχ : χ ∈ characterPairReps (H := Additive (integerCubicGaloisGroup S))) :
    ∃ (A : ℤ) (hA : A ≠ 0)
      (f : CuspForm (cubicThetaKernel (cubicNumeratorThetaLevel A)) 1),
      A ∣ (∏ a ∈ S, a) ^ 2 ∧
      (fun τ => f τ) = heckeTheta (cubicNumeratorHeckeCharacter A hA) ∧
      (∀ n : ℕ, (qExpansion 1 f).coeff n = idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n) ∧
      f ≠ 0 ∧
      ∀ (M : ℕ) (h₃ : 3 ∣ M) (U : Finset (ZMod M)ˣ),
        (∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1) →
        ∀ (ε : ℝ) (Φ : ℝ → ℝ), (∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1) →
        ∀ T : ℝ, 1 < T → T < 2 → Function.support Φ ⊆ Set.Ioo 1 T →
        ∀ᶠ x : ℝ in atTop,
          giantCubicTracePrimeTest U S χ ε Φ T x =
            giantCubicCuspPrimeTest f (fun p => giantUnitResidueIndicator U p) ε Φ T x := by
  classical
  obtain ⟨A, hA, f, hdiv, hform, hcoeff, hf, htrace⟩ :=
    cubicFourier_character_has_actual_cuspForm (fun a ha => (hS.2 a ha).1)
      χ (characterPairReps_nontrivial χ hχ)
  refine ⟨A, hA, f, hdiv, hform, hcoeff, hf, ?_⟩
  intro M h₃ U hU₃ ε Φ hΦ T hT₁ hT₂ hs
  let B := ∑ p ∈ giantCubicRamifiedPrimes S, p
  filter_upwards [giantSieveCandidates_structural_eventually hS U (fun _ => True) ε Φ
    hΦ hT₁ hT₂ hs, eventually_ge_atTop (B : ℝ)] with x hstruct hB
  unfold giantCubicTracePrimeTest giantCubicCuspPrimeTest
  apply Finset.sum_congr rfl
  intro p hp
  let w : ℂ := (giantSieveWeight Φ x p : ℂ) * giantUnitResidueIndicator U p *
    (((giantPrimeFactors (p - 1) x ε).card : ℝ) : ℂ)
  change w * giantCubicTraceAtPrime S χ p = w * (qExpansion 1 f).coeff p
  by_cases hw : w = 0
  · simp only [hw, zero_mul]
  have hweight : giantSieveWeight Φ x p ≠ 0 := by
    intro hz
    exact hw (by simp [w, hz])
  have hgiant : (giantPrimeFactors (p - 1) x ε).Nonempty := by
    by_contra hnone
    exact hw (by simp [w, Finset.not_nonempty_iff_eq_empty.mp hnone])
  have hu : ∃ v ∈ U, (v : ZMod M) = p := by
    by_contra hnone
    have hi : giantUnitResidueIndicator U p = 0 := by
      unfold giantUnitResidueIndicator
      exact ite_eq_right (fun h => hnone (Finset.mem_image.mp h))
    exact hw (by simp [w, hi])
  have hmem : p ∈ giantSieveCandidates U (fun _ => True) ε Φ T x :=
    mem_giantSieveCandidates.mpr ⟨hp, hu, trivial, hweight, hgiant⟩
  have hp' := hstruct p hmem
  have hp₃ : p % 3 = 1 := by
    obtain ⟨v, hv, hvp⟩ := hu
    have hmod := hU₃ v hv
    rw [hvp, map_natCast] at hmod
    exact ((ZMod.natCast_eq_natCast_iff' p 1 3).mp
      (by simpa only [Nat.cast_one] using hmod)).trans (by decide)
  have hgood : p ∉ giantCubicRamifiedPrimes S := by
    intro hram
    have hpB : p ≤ B := Finset.single_le_sum (f := fun n : ℕ => n)
      (fun _ _ => Nat.zero_le _) hram
    exact (not_le_of_gt hp'.2.1.1) ((Nat.cast_le.mpr hpB).trans hB)
  let : Fact p.Prime := ⟨hp'.1⟩
  let D := Classical.choice (exists_integralFrobeniusData (integerCubicField S) hp'.1)
  have hnonzero (a : ℤ) (ha : a ∈ S) : ¬ (p : ℤ) ∣ a := fun h =>
    hp'.2.2.1 a ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr h)
  apply congrArg (w * ·)
  simpa only [giantCubicTraceAtPrime, dite_eq_left hp'.1, dite_eq_left hp₃,
    ite_eq_left hgood, D] using (htrace p hp₃ D hnonzero).symm

end ArtinMatthews
