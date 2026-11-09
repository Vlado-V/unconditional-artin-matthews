module

public import ArtinMatthews.GiantCandidatePerformedSourceMomentAtRate
public import ArtinMatthews.GiantCandidatePerformedRetention


set_option backward.privateInPublic true
@[expose] public section

/-! The source selector allows independent signs and coefficient
orientations. The physical even moment uses their literal alternating
specialization on the same finite family. -/
namespace ArtinMatthews
open Filter
noncomputable section

theorem giantCandidateFullSelection_retained_eventually :
    ∀ᶠ x : ℝ in atTop,
      (Finset.univ : Finset (GiantCandidateGroupIndex x)) ∈
        giantCandidateRetainedOutcomes x giantCandidatePerformedLowerRate := by
  filter_upwards [giantCandidatePerformedUniv_lower_eventually] with x hx
  exact (giantCandidatePerformed_retained_iff _).mpr hx

theorem giantTwoSidedSourceAlternating_sign {step : ℤ} (hstep : step ≠ 0) (reverse : Bool) :
    let s := if reverse then -step.sign else step.sign
    s = 1 ∨ s = -1 := by
  rcases lt_or_gt_of_ne hstep with hn | hp
  · rw [Int.sign_eq_neg_one_of_neg hn]
    cases reverse <;> simp
  · rw [Int.sign_eq_one_of_pos hp]
    cases reverse <;> simp

theorem giantCandidatePerformedAlternatingMoment_eq_source {x : ℝ}
    (groups : Finset (GiantCandidateGroupIndex x)) {I : Type*} {k ell n : ℕ}
    (patterns : Finset I) (C : I → GiantCandidatePerformedBig groups → Finset (Fin k))
    (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient (giantCandidatePerformedBigBand groups) (C p) ell)
    (roots Z : Finset ℕ) :
    let reverse (i : Fin n) : Bool := decide (i.val%2 ≠ 0)
    let s (i : Fin n) := if reverse i then -step.sign else step.sign
    let c := fun p => giantCandidatePerformedPattern groups (C p)
    let u := fun p => giantCandidatePerformedCoefficient groups (K p)
    giantTwoSidedExpandedPhysicalMoment (fun _ : Fin n => patterns) (fun _ => c)
      (fun i => if i.val%2 = 0 then step else -step) q (fun i => if i.val%2 = 0 then ζ else -ζ)
      (fun i p a b aux => if i.val%2 = 0 then u p a b aux else star (u p b a aux)) roots Z =
    giantTwoSidedExpandedPhysicalMoment (fun _ : Fin n => patterns) (fun _ => c)
      (fun i => s i * (step.natAbs : ℤ)) q (fun i => if reverse i then -ζ else ζ)
      (fun i p => giantCandidatePerformedCoefficient groups (giantSignedOrientedCoefficient (reverse i) (K p))) roots Z := by
  intro reverse s c u
  have hκ : (fun i => s i * (step.natAbs : ℤ)) =
      fun i : Fin n => if i.val%2 = 0 then step else -step := by
    funext i
    by_cases hi : i.val%2 = 0
    · have hr : ¬ reverse i = true := by simp [reverse,hi]
      simp only [s, if_neg hr, if_pos hi, Int.sign_mul_natAbs]
    · have hr : reverse i = true := decide_eq_true hi
      simp only [s, if_pos hr, if_neg hi, neg_mul, Int.sign_mul_natAbs]
  have hζ : (fun i => if reverse i then -ζ else ζ) =
      fun i : Fin n => if i.val%2 = 0 then ζ else -ζ := by
    funext i
    by_cases hi : i.val%2 = 0 <;> simp [reverse,hi]
  have hK : (fun i p => giantCandidatePerformedCoefficient groups (giantSignedOrientedCoefficient (reverse i) (K p))) =
      fun (i : Fin n) p a b aux => if i.val%2 = 0 then u p a b aux else star (u p b a aux) := by
    funext i p a b aux
    by_cases hi : i.val%2 = 0 <;>
      simp [reverse,hi,u,giantSignedOrientedCoefficient,giantCandidatePerformedCoefficient]
  rw [hκ,hζ,hK]

end
end ArtinMatthews
