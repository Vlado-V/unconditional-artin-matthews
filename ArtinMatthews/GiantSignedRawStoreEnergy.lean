module

public import ArtinMatthews.GiantSignedEdgeEnergy
public import ArtinMatthews.GiantSignedRawCoupledPairing
public import ArtinMatthews.GiantSignedRawRareSplit
public import ArtinMatthews.GiantSignedSmallOmissions
public import ArtinMatthews.GiantSignedStateMemoryCutoff
public import ArtinMatthews.GiantSignedRawCoupledReverse
public import ArtinMatthews.GiantSignedRawStoreReverseRow
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The store energy obtains the omission gain after factorial reversal. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawProjectedStore_energy
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hsep : ∀ i j, Disjoint (PS i) (PB j))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v BS : ℝ}
    (hvmin : 0 < vmin) (hVMin : ∀ g, vmin ≤ V g) (hVMax : ∀ g, V g ≤ vmax)
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
    (θ ζ W : ℝ) (hW : 0 ≤ W) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ s r, ‖η s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N
      (giantSignedRawEdgeApply ν V (sign * kStep) q ρ θ ζ K
        (fun s r => η s r * giantSignedRawStoreOnlyMultiplier s r)
        (giantSignedStateMemoryCutoff N f))) ≤
      ENNReal.ofReal (W ^ 2 * ((N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)) *
        ((BS ^ Fintype.card S) ^ 2 *
          (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B)) *
        giantSignedStateEnergy PS ν f := by
  let κ : ℤ := sign * kStep
  let ε : ℝ := (N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)
  let A := giantSignedRawDegreeRowConstant S B ρ v vmin massMax BS (ell+budget)
  let R := (giantSignedEdgeReverseConstant vmin vmax (ell+budget)) ^ Fintype.card B
  let E := (BS ^ Fintype.card S) ^ 2 *
    (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B
  let fN := giantSignedStateMemoryCutoff N f
  let U := giantSignedRawEdgeApply ν V κ q ρ θ ζ K
    (fun s r => η s r * giantSignedRawStoreOnlyMultiplier s r) fN
  let F := giantSignedRawStoreSquareTest (C := C) v fN
  let F' := giantSignedRawCoupledFlip F
  have hA : 0 ≤ A := giantSignedRawDegreeRowConstant_nonneg hρ1 hv hBS
  have hR : 0 ≤ R := pow_nonneg (giantSignedEdgeReverseConstant_nonneg _ _ _) _
  have hε : 0 ≤ ε := div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg _)
  have hsymN := giantSignedStateMemoryCutoff_memory_symmetric N f hsym
  have hF : ∀ X Y s t, 0 ≤ F X Y s t := giantSignedRawStoreSquareTest_nonneg hv fN
  have hsF : ∀ X Y x a t m σ,
      F X Y (x,a,giantSignedMemoryPermute m σ) t = F X Y (x,a,m) t := by
    intro X Y x a t m σ
    rfl
  have htF : ∀ X Y s z b m σ,
      F X Y s (z,b,giantSignedMemoryPermute m σ) = F X Y s (z,b,m) := by
    intro X Y s z b m σ
    have he := hsymN z b m σ
    dsimp only [F, giantSignedRawStoreSquareTest, giantSignedRawMemoryWeight]
    change fN (z,b,giantSignedMemoryPermute m σ) = fN (z,b,m) at he
    rw [he]
    rfl
  have hmain : giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N U) ≤
      ENNReal.ofReal (W ^ 2 * A) * giantSignedRawCoupledPairing ν V κ q ρ F := by
    rw [giantSignedStateEnergy_eq_tsum, giantSignedRawCoupledPairing, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro s
    have hs := giantSignedRawStoreOnly_norm_sq_le hPS hPB hdis hVS hVB ν hν V hvmin hVMin
      hMass hq hq1 hBS hsmall hρ hρ1 hv budget hC κ θ ζ W hW K hK η hη fN s
    have hc := pow_le_pow_left₀ (norm_nonneg _)
      (giantSignedStateMemoryCutoff_norm_le N U s) 2
    have hm := giantSignedRawStateMass_nonneg hVS ν hν s
    apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hc.trans hs) hm)).trans_eq
    change ENNReal.ofReal (giantSignedStateMass PS ν s * (W ^ 2 * A *
      giantSignedRawCoupledRow ν V κ q ρ F s)) = _
    rw [mul_left_comm, ENNReal.ofReal_mul (mul_nonneg (sq_nonneg W) hA)]
  have hcol : giantSignedRawCoupledPairing ν V (-κ) q ρ F' ≤
      ENNReal.ofReal (ε * A) * giantSignedStateEnergy PS ν fN := by
    rw [giantSignedRawCoupledPairing, giantSignedStateEnergy_eq_tsum, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro s
    have hsign' : -sign = 1 ∨ -sign = -1 := by rcases hsign with h | h <;> simp [h]
    have hs : giantSignedRawCoupledRow ν V (-κ) q ρ F' s ≤ ε * A * ‖fN s‖ ^ 2 := by
      change giantSignedRawCoupledRow ν V (-κ) q ρ
        (fun X Y s t => giantSignedRawStoreSquareTest (C := C) v fN Y X t s) s ≤
          ε * A * ‖fN s‖ ^ 2
      have he := giantSignedRawReversedStoreRow_bound hPS hPB hdis hsep hVS hVB ν hν V hvmin hVMin
        hMass hq hq1 hBS hsmall hρ hρ1 hv budget hC N kStep hk (-sign) hsign'
        hstep tSmall tBig hlabels hgap hlower f s
      rw [neg_mul] at he
      exact he
    have hm := giantSignedRawStateMass_nonneg hVS ν hν s
    apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs hm)).trans_eq
    rw [mul_left_comm, ENNReal.ofReal_mul (mul_nonneg hε hA)]
  have hscalar : W ^ 2 * A * (R * (ε * A)) = W ^ 2 * ε * E := by
    dsimp only [A, R, E, giantSignedRawDegreeRowConstant, giantSignedEdgeEnergyConstant]
    rw [mul_pow, pow_right_comm _ 2 (Fintype.card B)]
    ring
  change giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N U) ≤
    ENNReal.ofReal (W ^ 2 * ε * E) * giantSignedStateEnergy PS ν f
  calc
    _ ≤ ENNReal.ofReal (W ^ 2 * A) * giantSignedRawCoupledPairing ν V κ q ρ F := hmain
    _ ≤ ENNReal.ofReal (W ^ 2 * A) * (ENNReal.ofReal R *
        giantSignedRawCoupledPairing ν V (-κ) q ρ F') :=
      mul_le_mul_right (giantSignedRawCoupledPairing_reverse_le hPS hVS hVB ν hν V
        hvmin hVMin hVMax κ hq.le hρ budget hC F hF hsF htF) _
    _ ≤ ENNReal.ofReal (W ^ 2 * A) * (ENNReal.ofReal R *
        (ENNReal.ofReal (ε * A) * giantSignedStateEnergy PS ν fN)) :=
      mul_le_mul_right (mul_le_mul_right hcol _) _
    _ = ENNReal.ofReal (W ^ 2 * ε * E) * giantSignedStateEnergy PS ν fN := by
      rw [← mul_assoc (ENNReal.ofReal R), ← ENNReal.ofReal_mul hR,
        ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg W) hA), hscalar]
    _ ≤ _ := mul_le_mul_right (giantSignedStateMemoryCutoff_energy_le ν N f) _

end
end ArtinMatthews
