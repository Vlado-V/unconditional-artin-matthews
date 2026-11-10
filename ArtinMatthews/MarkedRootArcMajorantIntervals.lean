module

public import ArtinMatthews.MarkedRootArcComplexity
public import ArtinMatthews.MarkedRawBadRootArcMajorant
public import ArtinMatthews.MarkedRootArcClipped
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact interval expressions for the positive pair and first-root
majorants. These keep signed frequencies, closed endpoints and all
fresh-law coefficients in their original positions. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPairRootArcMajorant_intervals (Q : Finset ℤ) (T : ℤ) (hT : T ≠ 0)
    {ε r : ℝ} (hε : ε < (1/2:ℝ)) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    markedPairRootArcMajorant Q T ε (r:AddCircle (1:ℝ)) =
      ∑ p : Q × Q,if p.1.1=p.2.1 then 0 else
        ∑ k ∈ markedRootArcCenters ((p.1.1-p.2.1)*T).natAbs,
          if r ∈ markedRootArcClippedInterval ((p.1.1-p.2.1)*T).natAbs ε k then (1:ℝ) else 0 := by
  unfold markedPairRootArcMajorant
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1.1=p.2.1
  · simp [markedPairRootArcSet,hp]
  · simp only [markedPairRootArcSet,ite_eq_right hp]
    exact markedBadRootMultiple_clipped_indicator _ (mul_ne_zero (sub_ne_zero.mpr hp) hT) hε hr₀ hr₁ 1

theorem markedPairRootArcComplexity_interval_count (Q : Finset ℤ) (T : ℤ) :
    markedPairRootArcComplexity Q T =
      ∑ p : Q × Q,if p.1.1=p.2.1 then 0 else
        ∑ _k ∈ markedRootArcCenters ((p.1.1-p.2.1)*T).natAbs,(1:ℝ) := by
  unfold markedPairRootArcComplexity
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · rfl
  · simp [markedRootArcCenters_card]

theorem markedRawFirstRootArcMajorant_intervals
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M : ℕ}
    (a : MarkedRawActive P M) (d₀ Y : ℝ) {r : ℝ}
    (hε : Y^(-7/10:ℝ) < (1/2:ℝ)) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    markedRawFirstRootArcMajorant a d₀ Y (r:AddCircle (1:ℝ)) =
      ∑ p : (markedRawDyadicOmissions a d₀) × ↥(Finset.Icc 1 ⌊Y^(1/5:ℝ)⌋₊),
        ∑ k ∈ markedRootArcCenters (markedSourceCopiedProduct (markedRawNumericActive a) p.1.1*p.2.1),
          if r ∈ markedRootArcClippedInterval
            (markedSourceCopiedProduct (markedRawNumericActive a) p.1.1*p.2.1) (Y^(-7/10:ℝ)) k then (1:ℝ) else 0 := by
  unfold markedRawFirstRootArcMajorant
  apply Finset.sum_congr rfl
  intro p _
  have hD : 0 < markedSourceCopiedProduct (markedRawNumericActive a) p.1.1 :=
    Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (a j k).1.2.pos))
  have hl : 0 < p.2.1 := (Finset.mem_Icc.mp p.2.2).1
  have hq : ((markedSourceCopiedProduct (markedRawNumericActive a) p.1.1*p.2.1:ℕ):ℤ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos hD hl).ne'
  simpa [markedFirstRootArcSet,Int.natAbs_mul] using
    markedBadRootMultiple_clipped_indicator _ hq hε hr₀ hr₁ (1:ℝ)

theorem markedRawBetaRootArcMajorant_intervals
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (a : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (hε : ∀ j,100*Real.exp (-((Real.log x)^(e j))) < (1/2:ℝ)) :
    markedRawBetaRootArcMajorant e x a (r:AddCircle (1:ℝ)) =
      ∑ p : Finset J × J,
        if p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2) then
          (∑ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ p.1) => e j.1) x,
            markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t *
              (∑ v : (markedRawDirtyFullTrials e x a (p.1.erase p.2)) × (markedRawDirtyFullTrials e x a (p.1.erase p.2)),
                if v.1.1=v.2.1 then 0 else
                  ∑ k ∈ markedRootArcCenters
                    ((v.1.1-v.2.1)*markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t).natAbs,
                    if r ∈ markedRootArcClippedInterval
                      ((v.1.1-v.2.1)*markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t).natAbs
                      (100*Real.exp (-((Real.log x)^(e p.2)))) k then (1:ℝ) else 0)) /
            Real.exp (-((Real.log x)^(e p.2))/4)
        else 0 := by
  unfold markedRawBetaRootArcMajorant
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    exact markedPairRootArcMajorant_intervals _ _ (markedFreshIntegerProduct_ne_zero _ _ t) (hε p.2) hr₀ hr₁
  · rfl

end
end ArtinMatthews
