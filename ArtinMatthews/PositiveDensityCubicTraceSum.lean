module

public import ArtinMatthews.PositiveDensityCubicPrimeTrace
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
public import Mathlib.Tactic.Basify
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

/-! Sum the true finite Fourier coefficients over the literal
prime-predecessor statistic on a split unit progression. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def giantCubicTracePrimeTest {M : ℕ} (U : Finset (ZMod M)ˣ)
    (S : Finset ℤ) (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x,
    (giantSieveWeight Φ x p : ℂ) * giantUnitResidueIndicator U p *
      (((giantPrimeFactors (p - 1) x ε).card : ℝ) : ℂ) * giantCubicTraceAtPrime S χ p

theorem giantSelectedPrimeTest_cubic_trace_expansion_eventually {S : Finset ℤ}
    (hS : AdmissibleBases S) {M : ℕ} (h₃ : 3 ∣ M) (U : Finset (ZMod M)ˣ)
    (hU₃ : ∀ v ∈ U, ZMod.castHom h₃ (ZMod 3) (v : ZMod M) = 1)
    (ε : ℝ) (Φ : ℝ → ℝ) (hΦ : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1)
    {T : ℝ} (hT₁ : 1 < T) (hT₂ : T < 2) (hs : Function.support Φ ⊆ Set.Ioo 1 T) :
    ∀ᶠ x : ℝ in atTop,
      giantSelectedPrimeTest U (giantCubicFrobeniusSelection S) ε Φ T x =
        (cubicConditionDensity S : ℂ) * giantUncenteredPrimeTest U ε Φ T x +
        ∑ χ ∈ characterPairReps (H := Additive (integerCubicGaloisGroup S)),
          ((indicatorFourierCoeff (cubicConditionFinset S) χ).re : ℂ) *
            giantCubicTracePrimeTest U S χ ε Φ T x := by
  classical
  let B := ∑ p ∈ giantCubicRamifiedPrimes S, p
  filter_upwards [giantSieveCandidates_structural_eventually hS U (fun _ => True) ε Φ
    hΦ hT₁ hT₂ hs, eventually_ge_atTop (B : ℝ)] with x hstruct hB
  let w (p : ℕ) : ℂ := (giantSieveWeight Φ x p : ℂ) * giantUnitResidueIndicator U p *
    (((giantPrimeFactors (p - 1) x ε).card : ℝ) : ℂ)
  let R := characterPairReps (H := Additive (integerCubicGaloisGroup S))
  let c (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) : ℂ :=
    ((indicatorFourierCoeff (cubicConditionFinset S) χ).re : ℂ)
  have hpoint (p : ℕ) (hp : p ∈ giantPrimeMeanRange T x) :
      (if giantCubicFrobeniusSelection S p then w p else 0) =
        (cubicConditionDensity S : ℂ) * w p +
          ∑ χ ∈ R, c χ * (w p * giantCubicTraceAtPrime S χ p) := by
    by_cases hw : w p = 0
    · simp [hw]
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
    have hgate : (if giantCubicFrobeniusSelection S p then w p else 0) =
        (if giantCubicFrobeniusSelection S p then (1 : ℂ) else 0) * w p := by
      split_ifs <;> simp
    rw [hgate, giantCubicFrobeniusSelection_trace_expansion hp'.1 hp₃ hp'.2.2.1 hgood,
      add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro χ _hχ
    change (c χ * giantCubicTraceAtPrime S χ p) * w p = c χ * (w p * giantCubicTraceAtPrime S χ p)
    ring
  change (∑ p ∈ giantPrimeMeanRange T x, if giantCubicFrobeniusSelection S p then w p else 0) =
    (cubicConditionDensity S : ℂ) * (∑ p ∈ giantPrimeMeanRange T x, w p) +
      ∑ χ ∈ R, c χ * ∑ p ∈ giantPrimeMeanRange T x, w p * giantCubicTraceAtPrime S χ p
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := R) (t := giantPrimeMeanRange T x), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hpoint

end ArtinMatthews
