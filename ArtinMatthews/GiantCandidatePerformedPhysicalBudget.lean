module

public import ArtinMatthews.GiantCandidatePerformedReturnJoin
public import ArtinMatthews.GiantTwoSidedUniformRootTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! Restore the original physical root statistic after the independent
return moment has been bounded, at the literal interval length. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators
noncomputable section
universe u

theorem giantCandidatePerformedPhysical_norm_eventually_of_independent
    (k ell m : ℕ) (C₁ Cstep E : ℝ) (hE : 0 ≤ E) {q γ : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ groups : Finset (GiantCandidateGroupIndex x),
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes (fun j : ↥groups => giantCandidateGroup x j.val)),
        NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes (fun j : ↥groups => giantCandidateGroup x j.val)),
        NeZero p.val := nz
      let n := giantTwoSidedSourceMomentLength x
      let L := Real.log x
      ∀ (I : Type u) (patterns : Fin n → Finset I)
        (C : Fin n → I → GiantCandidatePerformedBig groups → Finset (Fin k)),
        (∀ i p, p ∈ patterns i → ∀ g, (C i p g).card ≤ m) →
      ∀ (κ : Fin n → ℤ), (∀ i, ((κ i).natAbs : ℝ) ≤ L^Cstep) →
      ∀ (ζ : Fin n → ℝ) (K : ∀ i p,
        GiantTwoSidedPatternCoefficient (giantCandidatePerformedBigBand groups) (C i p) ell)
        (W : ℝ), 0 ≤ W →
        (∀ i p, p ∈ patterns i → ∀ a b aux, ‖K i p a b aux‖ ≤ W) →
        (∀ i, ((patterns i).card : ℝ)*W ≤ L^C₁) →
      let c := fun i p => giantCandidatePerformedPattern groups (C i p)
      let u := fun i p => giantCandidatePerformedCoefficient groups (K i p)
      ‖giantTwoSidedExpandedIndependentMoment patterns c κ q ζ u‖ ≤ (L^(-(E+1)))^n →
      ∀ X : ℝ, x^γ ≤ X →
        ‖giantTwoSidedExpandedPhysicalMoment patterns c κ q ζ u
          (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X)‖ /
          ((⌈2*X⌉₊-⌈X⌉₊ : ℕ) : ℝ) ≤ (L^(-E))^n := by
  have hE' : 0 ≤ E+1 := by linarith
  filter_upwards [giantCandidateUniformWeightedRootTransfer.{u} k ell m C₁ Cstep (E+1) hE' hγ hq hq1,
    giantCandidateRootInterval_budget hγ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))] with x hCRT hinterval hL
  intro groups nz
  letI := nz
  try dsimp only
  intro I patterns C hC κ hκ ζ K W hW hK hCost hindep X hX
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let c := fun i p => giantCandidatePerformedPattern groups (C i p)
  let u := fun i p => giantCandidatePerformedCoefficient groups (K i p)
  have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 2).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hn : 1 ≤ n := giantTwoSidedSourceMomentLength_pos hL0
  have hlen : (0 : ℝ) < ((⌈2*X⌉₊-⌈X⌉₊ : ℕ) : ℝ) := (Real.exp_pos _).trans_le (hinterval X hX).2
  have hcap (i : Fin n) (p : I) (hp : p ∈ patterns i) (j : ↥groups) : (c i p j).card ≤ m := by
    rcases j with ⟨j | j, hj⟩
    · simp only [c, giantCandidatePerformedPattern, Finset.card_empty, Nat.zero_le]
    · exact hC i p hp ⟨j,hj⟩
  have hcoef (i : Fin n) (p : I) (hp : p ∈ patterns i) : 0 ≤ W ∧ ∀ a b aux, ‖u i p a b aux‖ ≤ W :=
    ⟨hW, fun _ _ _ => hK i p hp _ _ _⟩
  have hmass (i : Fin n) : (∑ _p ∈ patterns i, W) ≤ L^C₁ := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using hCost i
  have herr := hCRT groups nz I patterns c hcap κ hκ ζ u (fun _ _ => W) hcoef hmass X hX
  rw [Real.rpow_mul_natCast hL0.le] at herr
  have h := giantCandidatePerformedPhysicalMoment_norm_div_le groups patterns C κ q ζ K X hlen herr hindep
  have h2 : (2 : ℝ) ≤ L^n := hL.trans (by simpa only [pow_one] using pow_le_pow_right₀ hL1 hn)
  have he : L*L^(-(E+1)) = L^(-E) := by
    calc
      _ = L^(1 : ℝ)*L^(-(E+1)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hL0]; congr 1; ring
  calc
    _ ≤ (L^(-(E+1)))^n+(L^(-(E+1)))^n := h
    _ = 2*(L^(-(E+1)))^n := by ring
    _ ≤ L^n*(L^(-(E+1)))^n := mul_le_mul_of_nonneg_right h2 (pow_nonneg (Real.rpow_nonneg hL0.le _) _)
    _ = _ := by rw [← mul_pow, he]

end
end ArtinMatthews
