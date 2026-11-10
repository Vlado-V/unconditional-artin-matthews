module

public import ArtinMatthews.MarkedTypeIIPadCollisions
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual lifespan baseline and its tilted fresh-prime law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedVisitLoss {n : ℕ} (q : Fin n → ℝ) : ℝ := ∑ i, (1 - q i)

def giantSignedPrimeBaseline {n : ℕ} (q : Fin n → ℝ) (p : ℕ) : ℝ :=
  1 - giantSignedVisitLoss q / p

def giantSignedPrimeDensity {n : ℕ} (q : Fin n → ℝ) (p : ℕ) : ℝ :=
  (giantSignedPrimeBaseline q p)⁻¹

def giantSignedTiltedPrimeLaw (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ) (p : P) : ℝ :=
  markedHarmonicAtom P p / giantSignedPrimeBaseline q p.val

theorem giantSignedTiltedPrimeLaw_eq (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ) (p : P) :
    giantSignedTiltedPrimeLaw P q p = markedHarmonicAtom P p * giantSignedPrimeDensity q p.val := rfl

theorem giantSignedVisitLoss_nonneg {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, q i ≤ 1) :
    0 ≤ giantSignedVisitLoss q :=
  Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hq i)

theorem giantSignedVisitLoss_le {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) :
    giantSignedVisitLoss q ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by linarith [hq i])
    _ = _ := by simp

theorem giantSignedPrimeBaseline_bounds {n p : ℕ} (q : Fin n → ℝ)
    (hp : 0 < p) (hq : ∀ i, q i ≤ 1) {δ : ℝ}
    (hδ : giantSignedVisitLoss q / p ≤ δ) (hδ1 : δ < 1) :
    0 < giantSignedPrimeBaseline q p ∧
      1 - δ ≤ giantSignedPrimeBaseline q p ∧ giantSignedPrimeBaseline q p ≤ 1 := by
  have hratio : 0 ≤ giantSignedVisitLoss q / p :=
    div_nonneg (giantSignedVisitLoss_nonneg q hq) (by exact_mod_cast hp.le)
  unfold giantSignedPrimeBaseline
  constructor
  · linarith
  constructor <;> linarith

theorem giantSignedPrimeDensity_bounds {n p : ℕ} (q : Fin n → ℝ)
    (hp : 0 < p) (hq : ∀ i, q i ≤ 1) {δ : ℝ}
    (hδ : giantSignedVisitLoss q / p ≤ δ) (hδ1 : δ < 1) :
    1 ≤ giantSignedPrimeDensity q p ∧ giantSignedPrimeDensity q p ≤ (1 - δ)⁻¹ := by
  obtain ⟨hb, hlo, hhi⟩ := giantSignedPrimeBaseline_bounds q hp hq hδ hδ1
  unfold giantSignedPrimeDensity
  constructor
  · have h : (1 : ℝ) ≤ 1 / giantSignedPrimeBaseline q p :=
      (le_div_iff₀ hb).mpr (by simpa only [one_mul] using hhi)
    simpa only [one_div, one_mul] using h
  · simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hδ1) hlo

theorem giantSignedPrimeBaseline_pos_of_length {n p : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : n < p) : 0 < giantSignedPrimeBaseline q p := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le n) hp)
  have hnp : (n : ℝ) < p := by exact_mod_cast hp
  have hlt : giantSignedVisitLoss q / p < 1 :=
    (div_lt_one hp0).mpr ((giantSignedVisitLoss_le q hq).trans_lt hnp)
  exact sub_pos.mpr hlt

theorem giantSignedTiltedPrimeLaw_pos (P : Finset ℕ) {n : ℕ} (q : Fin n → ℝ)
    (hV : 0 < bandReciprocalMass P) (hq : ∀ i, 0 ≤ q i)
    (hp : ∀ p : P, n < p.val) (p : P) : 0 < giantSignedTiltedPrimeLaw P q p := by
  unfold giantSignedTiltedPrimeLaw
  apply div_pos _ (giantSignedPrimeBaseline_pos_of_length q hq (hp p))
  unfold markedHarmonicAtom
  exact div_pos (one_div_pos.mpr (by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le n) (hp p)))) hV

end
end ArtinMatthews
