module

public import ArtinMatthews.GiantSignedRawCoupledRow
public import ArtinMatthews.GiantSignedRawPromoteNorm
public import ArtinMatthews.GiantSignedRawWeightedRows


set_option backward.privateInPublic true
@[expose] public section

/-! The store row square uses the original store ban in the paired test. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawStoreSquareTest
    (v : ℝ) (f : GiantSignedState PS PB (k+ell) → ℂ) : GiantSignedRawCoupledTest PS PB C ell :=
  fun X Y s t => if X ≠ (fun _ => ∅) ∧ Y = (fun _ => ∅) then
    giantSignedRawMemoryWeight v s * (‖f t‖ ^ 2 / giantSignedRawMemoryWeight v t)
  else 0

theorem giantSignedRawStoreSquareTest_nonneg
    {v : ℝ} (hv : 1 ≤ v) (f : GiantSignedState PS PB (k+ell) → ℂ) :
    ∀ X Y s t, 0 ≤ giantSignedRawStoreSquareTest (C := C) v f X Y s t := by
  intro X Y s t
  unfold giantSignedRawStoreSquareTest
  split_ifs
  · exact mul_nonneg (giantSignedRawMemoryWeight_pos hv s).le
      (div_nonneg (sq_nonneg _) (giantSignedRawMemoryWeight_pos hv t).le)
  · exact le_rfl

theorem giantSignedRawStoreOnly_norm_sq_le
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ v BS : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hsmall : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget) (κ : ℤ)
    (θ ζ W : ℝ) (hW : 0 ≤ W) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ s r, ‖η s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    ‖giantSignedRawEdgeApply ν V κ q ρ θ ζ K
      (fun s r => η s r * giantSignedRawStoreOnlyMultiplier s r) f s‖ ^ 2 ≤
      W ^ 2 * giantSignedRawDegreeRowConstant S B ρ v vmin massMax BS (ell+budget) *
        giantSignedRawCoupledRow ν V κ q ρ (giantSignedRawStoreSquareTest (C := C) v f) s := by
  let R := GiantSignedRawEdgeMove PS PB ell C s.2.2
  let A := giantSignedRawDegreeRowConstant S B ρ v vmin massMax BS (ell+budget)
  let φ := giantSignedRawMemoryWeight (PS := PS) (PB := PB) (M := k+ell) v
  let t (r : R) := giantSignedRawEdgeTarget κ s r
  let p (r : R) := giantSignedRawPositiveCoefficient ν V κ q ρ s r
  let ban (r : R) := GiantSignedEdgePromotionBan (giantSignedRawEdgeProduct s r) r.choice.1
    (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r))
  let keep (r : R) : Prop := r.choice.1 ≠ (fun _ => ∅) ∧ r.choice.2.1 = (fun _ => ∅)
  let w (r : R) := if keep r ∧ ban r then p r else 0
  let U := giantSignedRawEdgeApply ν V κ q ρ θ ζ K
    (fun s r => η s r * giantSignedRawStoreOnlyMultiplier s r) f s
  have hp (r : R) : 0 ≤ p r := giantSignedRawPositiveCoefficient_nonneg hVB ν V κ q ρ s r
  have hw (r : R) : 0 ≤ w r := by
    unfold w
    split_ifs
    · exact hp r
    · exact le_rfl
  have hφ (a : GiantSignedState PS PB (k+ell)) : 0 < φ a := giantSignedRawMemoryWeight_pos hv a
  have hterm (r : R) :
      ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r *
        (η s r * giantSignedRawStoreOnlyMultiplier s r) * f (t r)‖ ≤ W * (w r * ‖f (t r)‖) := by
    by_cases hr : keep r ∧ ban r
    · dsimp only [w]
      rw [if_pos hr, ← mul_assoc W (p r), norm_mul, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hmult : ‖η s r * giantSignedRawStoreOnlyMultiplier s r‖ ≤ 1 := by
        rw [norm_mul]
        calc
          _ ≤ 1 * ‖giantSignedRawStoreOnlyMultiplier s r‖ :=
            mul_le_mul_of_nonneg_right (hη s r) (norm_nonneg _)
          _ ≤ _ := by simpa only [one_mul] using giantSignedRawStoreOnlyMultiplier_norm s r
      calc
        _ ≤ ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r‖ * 1 :=
          mul_le_mul_of_nonneg_left hmult (norm_nonneg _)
        _ ≤ _ := by
          rw [mul_one]
          exact giantSignedRawEdgeCoefficient_norm_le_positiveCoefficient hPS hPB hVS hVB
            ν V κ hq.le ρ θ ζ W hW K hK s r
    · dsimp only [w]
      rw [if_neg hr, zero_mul, mul_zero]
      by_cases hc : giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r = 0
      · simp only [hc, zero_mul, norm_zero, le_refl]
      have hb : ban r := (giantSignedRawEdgeCoefficient_conditions ν V κ q ρ θ ζ K s r hc).1.2.2.2.1
      have hkeep : ¬ keep r := fun h => hr ⟨h,hb⟩
      by_cases hT : r.choice.2.1 = (fun _ => ∅)
      · have hS : r.choice.1 = (fun _ => ∅) := not_not.mp (fun hS => hkeep ⟨hS,hT⟩)
        simp only [giantSignedRawStoreOnlyMultiplier, hT, hS, ite_true, mul_zero, zero_mul,
          norm_zero, le_refl]
      · simp only [giantSignedRawStoreOnlyMultiplier, hT, ite_false, mul_zero, zero_mul,
          norm_zero, le_refl]
  have hnorm : ‖U‖ ≤ W * ∑ r : R, w r * ‖f (t r)‖ := by
    unfold U giantSignedRawEdgeApply
    rw [Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun r _ => hterm r)
  have hcs : (∑ r : R, w r * ‖f (t r)‖) ^ 2 ≤
      (∑ r : R, w r * φ (t r)) * (∑ r : R, w r * (‖f (t r)‖ ^ 2 / φ (t r))) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · exact fun r _ => mul_nonneg (hw r) (hφ (t r)).le
    · exact fun r _ => mul_nonneg (hw r) (div_nonneg (sq_nonneg _) (hφ (t r)).le)
    · intro r _
      exact le_of_eq (by field_simp [(hφ (t r)).ne'] <;> ring)
  have hrow : (∑ r : R, w r * φ (t r)) ≤ A * φ s := by
    have hg := giantSignedRawPositiveWeightedGate_bound hPS hdis hVS hVB ν hν V hvmin hVmin
      hMass hq hq1 hBS hsmall hρ hρ1 hv budget hC κ (fun _ => True) s
    simp only [ite_true, giantSignedRawOuterWeight_sum C hVB, one_mul] at hg
    apply le_trans _ hg
    apply Finset.sum_le_sum
    intro r _
    apply mul_le_mul_of_nonneg_right _ (hφ (t r)).le
    unfold w
    split_ifs
    · exact le_rfl
    · exact hp r
  have hpair : giantSignedRawCoupledRow ν V κ q ρ (giantSignedRawStoreSquareTest (C := C) v f) s =
      φ s * ∑ r : R, w r * (‖f (t r)‖ ^ 2 / φ (t r)) := by
    unfold giantSignedRawCoupledRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    change p r * (if ban r then
        if keep r then φ s * (‖f (t r)‖ ^ 2 / φ (t r)) else 0 else 0) = _
    by_cases hb : ban r <;> by_cases hk : keep r <;>
      simp only [w, hb, hk, true_and, and_true, false_and, and_false,
        ite_true, ite_false, zero_mul, mul_zero] <;> ring
  change ‖U‖ ^ 2 ≤ W ^ 2 * A * _
  calc
    _ ≤ (W * ∑ r : R, w r * ‖f (t r)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm _
    _ = W ^ 2 * (∑ r : R, w r * ‖f (t r)‖) ^ 2 := mul_pow _ _ _
    _ ≤ W ^ 2 * ((∑ r : R, w r * φ (t r)) *
        (∑ r : R, w r * (‖f (t r)‖ ^ 2 / φ (t r)))) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg W)
    _ ≤ W ^ 2 * ((A * φ s) * (∑ r : R, w r * (‖f (t r)‖ ^ 2 / φ (t r)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrow
        (Finset.sum_nonneg fun r _ => mul_nonneg (hw r)
          (div_nonneg (sq_nonneg _) (hφ (t r)).le))) (sq_nonneg W)
    _ = _ := by rw [hpair]; ring

end
end ArtinMatthews
