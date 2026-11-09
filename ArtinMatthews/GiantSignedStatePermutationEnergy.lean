module

public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedEdgePermutation
public import ArtinMatthews.IdealProductAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform endpoint slot averaging preserves the original small Haar
and big product measure for every nonnegative big prime law. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

def giantSignedStatePermute (πS : S → Equiv.Perm (Fin M))
    (πB : B → Equiv.Perm (Fin M)) :
    GiantSignedState PS PB M ≃ GiantSignedState PS PB M :=
  Equiv.prodCongr (giantTwoSidedResiduePermute πS)
    (Equiv.prodCongr (giantSignedGroupedTuplePermutation πB) (Equiv.refl _))

omit [Fintype S] [DecidableEq S] [DecidableEq B]
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedActiveMass_slot_permute
    (ν : ∀ g, PB g → ℝ) (π : B → Equiv.Perm (Fin M))
    (a : MarkedPhysicalMarking PB M) :
    giantSignedActiveMass ν (giantSignedGroupedTuplePermutation π a) =
      giantSignedActiveMass ν a := by
  unfold giantSignedActiveMass
  apply Finset.prod_congr rfl
  intro g _
  exact Equiv.prod_comp (π g) (fun i => ν g (a g i))

omit [DecidableEq S] [DecidableEq B]
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedStateMass_slot_permute
    (ν : ∀ g, PB g → ℝ) (πS : S → Equiv.Perm (Fin M))
    (πB : B → Equiv.Perm (Fin M)) (s : GiantSignedState PS PB M) :
    giantSignedStateMass PS ν (giantSignedStatePermute PS πS πB s) =
      giantSignedStateMass PS ν s := by
  rcases s with ⟨s,a,m⟩
  change giantTwoSidedResidueHaarStateMass PS M *
      giantSignedActiveMass ν (giantSignedGroupedTuplePermutation πB a) *
        giantSignedMemoryMass ν m =
      giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a *
        giantSignedMemoryMass ν m
  rw [giantSignedActiveMass_slot_permute]

theorem giantSignedStateEnergy_eq_tsum
    (ν : ∀ g, PB g → ℝ) (f : GiantSignedState PS PB M → ℂ) :
    giantSignedStateEnergy PS ν f =
      ∑' s : GiantSignedState PS PB M,
        ENNReal.ofReal (giantSignedStateMass PS ν s * ‖f s‖ ^ 2) := by
  classical
  unfold giantSignedStateEnergy
  symm
  rw [ENNReal.tsum_prod']
  simp only [ENNReal.tsum_prod']
  calc
    _ = ∑' s : GiantTwoSidedResidueState PS M, ∑' m : GiantSignedMemory PB,
        ∑' a : MarkedPhysicalMarking PB M,
          ENNReal.ofReal (giantSignedStateMass PS ν (s,a,m) * ‖f (s,a,m)‖ ^ 2) :=
      tsum_congr (fun _ => ENNReal.tsum_comm)
    _ = ∑' m : GiantSignedMemory PB, ∑' s : GiantTwoSidedResidueState PS M,
        ∑' a : MarkedPhysicalMarking PB M,
          ENNReal.ofReal (giantSignedStateMass PS ν (s,a,m) * ‖f (s,a,m)‖ ^ 2) :=
      ENNReal.tsum_comm
    _ = _ := by simp only [tsum_fintype]

theorem giantSignedStateEnergy_slot_permute
    (ν : ∀ g, PB g → ℝ) (πS : S → Equiv.Perm (Fin M))
    (πB : B → Equiv.Perm (Fin M)) (f : GiantSignedState PS PB M → ℂ) :
    giantSignedStateEnergy PS ν (fun s => f (giantSignedStatePermute PS πS πB s)) =
      giantSignedStateEnergy PS ν f := by
  rw [giantSignedStateEnergy_eq_tsum, giantSignedStateEnergy_eq_tsum]
  simpa only [giantSignedStateMass_slot_permute] using
    (giantSignedStatePermute PS πS πB).tsum_eq
      (fun s => ENNReal.ofReal (giantSignedStateMass PS ν s * ‖f s‖ ^ 2))

abbrev GiantSignedStateSlotPermutations (S B : Type*) (M : ℕ) :=
  (S → Equiv.Perm (Fin M)) × (B → Equiv.Perm (Fin M))

def giantSignedStateSlotAverage (f : GiantSignedState PS PB M → ℂ)
    (s : GiantSignedState PS PB M) : ℂ :=
  ∑ π : GiantSignedStateSlotPermutations S B M,
    (((Fintype.card (GiantSignedStateSlotPermutations S B M) : ℝ)⁻¹ : ℝ) : ℂ) *
      f (giantSignedStatePermute PS π.1 π.2 s)

theorem giantSignedStateEnergy_probability_average {I : Type*} [Fintype I]
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (F : I → GiantSignedState PS PB M → ℂ) :
    giantSignedStateEnergy PS ν (fun s => ∑ i, (w i : ℂ) * F i s) ≤
      ∑ i, ENNReal.ofReal (w i) * giantSignedStateEnergy PS ν (F i) := by
  classical
  have hstate (s : GiantSignedState PS PB M) : 0 ≤ giantSignedStateMass PS ν s := by
    apply mul_nonneg
    · apply mul_nonneg
      · unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
        exact div_nonneg
          (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _))
          (Nat.cast_nonneg _)
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hν g _))
    · exact giantSignedMemoryMass_nonneg ν hν s.2.2
  have hpoint (s : GiantSignedState PS PB M) :
      ENNReal.ofReal (giantSignedStateMass PS ν s * ‖∑ i, (w i : ℂ) * F i s‖ ^ 2) ≤
        ∑ i, ENNReal.ofReal (w i) *
          ENNReal.ofReal (giantSignedStateMass PS ν s * ‖F i s‖ ^ 2) := by
    have hj := idealWeightedJensen w hw hsum (fun i => F i s)
    apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hj (hstate s))).trans_eq
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
      (fun i _ => mul_nonneg (hstate s) (mul_nonneg (hw i) (sq_nonneg _)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [← ENNReal.ofReal_mul (hw i)]
    congr 1
    ring
  rw [giantSignedStateEnergy_eq_tsum]
  calc
    _ ≤ ∑' s : GiantSignedState PS PB M, ∑ i, ENNReal.ofReal (w i) *
        ENNReal.ofReal (giantSignedStateMass PS ν s * ‖F i s‖ ^ 2) :=
      ENNReal.tsum_le_tsum hpoint
    _ = ∑' s : GiantSignedState PS PB M, ∑' i : I, ENNReal.ofReal (w i) *
        ENNReal.ofReal (giantSignedStateMass PS ν s * ‖F i s‖ ^ 2) := by
      simp only [tsum_fintype]
    _ = ∑' i : I, ∑' s : GiantSignedState PS PB M, ENNReal.ofReal (w i) *
        ENNReal.ofReal (giantSignedStateMass PS ν s * ‖F i s‖ ^ 2) := ENNReal.tsum_comm
    _ = _ := by
      simp only [tsum_fintype, ENNReal.tsum_mul_left, giantSignedStateEnergy_eq_tsum]

theorem giantSignedStateSlotAverage_energy
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f : GiantSignedState PS PB M → ℂ) :
    giantSignedStateEnergy PS ν (giantSignedStateSlotAverage PS f) ≤
      giantSignedStateEnergy PS ν f := by
  let A := GiantSignedStateSlotPermutations S B M
  let W : ℝ := (Fintype.card A : ℝ)⁻¹
  have hn : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hW : 0 ≤ W := inv_nonneg.mpr hn.le
  have hsum : (∑ _π : A, W) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, W]
    exact mul_inv_cancel₀ hn.ne'
  have he := giantSignedStateEnergy_probability_average PS hV ν hν
    (fun _ : A => W) (fun _ => hW) hsum
    (fun π s => f (giantSignedStatePermute PS π.1 π.2 s))
  apply he.trans_eq
  simp_rw [giantSignedStateEnergy_slot_permute]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hW), hsum,
    ENNReal.ofReal_one, one_mul]

end
end ArtinMatthews
