module

public import ArtinMatthews.GiantSignedRawStoreSquare
public import ArtinMatthews.GiantSignedStateMemoryCutoff
public import ArtinMatthews.GiantSignedRawPositiveRareGate
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! The transposed store test is supported on the actual capped promotion gate. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawReversedStoreRow_bound
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hsep : ∀ i j, Disjoint (PS i) (PB j))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ v BS : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hsmall : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (N kStep : ℕ) (hk : 0 < kStep) (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (hstep : ∀ j p, p ∈ PB j → kStep < p)
    (tSmall tBig : ℝ) (hlabels : ∀ j p, p ∈ PS j → (p : ℝ) ≤ Real.exp tSmall)
    (hgap : (ell : ℝ) * (Fintype.card S : ℝ) * tSmall < tBig)
    (hlower : ∀ j p, p ∈ PB j → Real.exp tBig ≤ (p : ℝ))
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawCoupledRow ν V (sign * kStep) q ρ
        (fun X Y s t => giantSignedRawStoreSquareTest (C := C) v
          (giantSignedStateMemoryCutoff N f) Y X t s) s ≤
      ((N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)) *
        giantSignedRawDegreeRowConstant S B ρ v vmin massMax BS (ell+budget) *
          ‖giantSignedStateMemoryCutoff N f s‖ ^ 2 := by
  let R := GiantSignedRawEdgeMove PS PB ell C s.2.2
  let κ : ℤ := sign * kStep
  let ε : ℝ := (N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)
  let A := giantSignedRawDegreeRowConstant S B ρ v vmin massMax BS (ell+budget)
  let φ := giantSignedRawMemoryWeight (PS := PS) (PB := PB) (M := k+ell) v
  let fN := giantSignedStateMemoryCutoff N f
  let g := ‖fN s‖ ^ 2 / φ s
  let p (r : R) := giantSignedRawPositiveCoefficient ν V κ q ρ s r
  let t (r : R) := giantSignedRawEdgeTarget κ s r
  let ban (r : R) := GiantSignedEdgePromotionBan (giantSignedRawEdgeProduct s r) r.choice.1
    (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r))
  let gate := GiantSignedRawOuterCappedSourceGate (C := C) N κ s
  let W (r : R) := p r * (if gate (giantSignedRawMoveOuter r) then φ (t r) else 0)
  have hφ (a : GiantSignedState PS PB (k+ell)) : 0 < φ a := giantSignedRawMemoryWeight_pos hv a
  have hg : 0 ≤ g := div_nonneg (sq_nonneg _) (hφ s).le
  have hp (r : R) : 0 ≤ p r := giantSignedRawPositiveCoefficient_nonneg hVB ν V κ q ρ s r
  have hW (r : R) : 0 ≤ W r := by
    unfold W
    refine mul_nonneg (hp r) ?_
    split_ifs
    · exact (hφ (t r)).le
    · exact le_rfl
  have hterm (r : R) :
      p r * (if ban r then
        if r.choice.2.1 ≠ (fun _ => ∅) ∧ r.choice.1 = (fun _ => ∅) then φ (t r) * g else 0
      else 0) ≤ W r * g := by
    by_cases hb : ban r
    · rw [if_pos hb]
      by_cases ht : r.choice.2.1 ≠ (fun _ => ∅) ∧ r.choice.1 = (fun _ => ∅)
      · rw [if_pos ht]
        by_cases hn : (∑ j, s.2.2.1 j) ≤ N
        · by_cases hz : p r = 0
          · simp only [W, hz, zero_mul, le_refl]
          have hr := giantSignedRawPositiveCoefficient_promotion_sourceRareGate ν V κ q ρ s r hz ht.1
          have he : gate (giantSignedRawMoveOuter r) :=
            ⟨hn, (giantSignedRawSourceRareGate_outer κ s r).mp hr⟩
          dsimp only [W]
          rw [if_pos he, mul_assoc]
        · have he : fN s = 0 := giantSignedStateMemoryCutoff_of_lt N f s (lt_of_not_ge hn)
          simp only [g, he, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero, le_refl]
      · simpa only [if_neg ht, mul_zero] using mul_nonneg (hW r) hg
    · simpa only [if_neg hb, mul_zero] using mul_nonneg (hW r) hg
  have hrow : (∑ r : R, W r) ≤ ε * (A * φ s) := by
    have he := giantSignedRawPositiveWeightedGate_bound hPS hdis hVS hVB ν hν V hvmin hVmin
      hMass hq hq1 hBS hsmall hρ hρ1 hv budget hC κ gate s
    apply he.trans
    have hA : 0 ≤ A := giantSignedRawDegreeRowConstant_nonneg hρ1 hv hBS
    exact mul_le_mul_of_nonneg_right
      (giantSignedRawOuterCappedSourceGate_mass (C := C) hPS hPB hdis hsep hVB
        N kStep hk sign hsign hstep tSmall tBig hlabels hgap hlower s)
      (mul_nonneg hA (hφ s).le)
  change giantSignedRawCoupledRow ν V κ q ρ
    (fun X Y s t => giantSignedRawStoreSquareTest (C := C) v fN Y X t s) s ≤ ε * A * ‖fN s‖ ^ 2
  calc
    _ ≤ (∑ r : R, W r) * g := by
      unfold giantSignedRawCoupledRow
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun r _ => hterm r)
    _ ≤ (ε * (A * φ s)) * g := mul_le_mul_of_nonneg_right hrow hg
    _ = _ := by
      dsimp only [g]
      field_simp [(hφ s).ne'] <;> ring

end
end ArtinMatthews
