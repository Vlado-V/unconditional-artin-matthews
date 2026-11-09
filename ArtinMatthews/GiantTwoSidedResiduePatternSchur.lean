module

public import ArtinMatthews.GiantTwoSidedResiduePatternRows
public import ArtinMatthews.GiantTwoSidedPatternAbsoluteActual


set_option backward.privateInPublic true
@[expose] public section

/-! The actual candidate groups give a fixed logarithmic absolute Schur
bound on full residue states, uniformly in the copied-list length. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedResidueSlotAverage {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ}
    (K : GiantTwoSidedResidueState P M → GiantTwoSidedResidueState P M → ℝ)
    (s t : GiantTwoSidedResidueState P M) : ℝ :=
  let Permutations := J → Equiv.Perm (Fin M)
  (∑ π : Permutations,∑ τ : Permutations,K (giantTwoSidedResiduePermute π s)
    (giantTwoSidedResiduePermute τ t))/(Fintype.card Permutations:ℝ)^2

theorem giantTwoSidedResidueSlotAverage_row_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val] {M : ℕ}
    (K : GiantTwoSidedResidueState P M → GiantTwoSidedResidueState P M → ℝ)
    {B : ℝ} (hK : ∀ s,∑ t,K s t≤B) (s : GiantTwoSidedResidueState P M) :
    (∑ t,giantTwoSidedResidueSlotAverage K s t)≤B := by
  let Permutations := J → Equiv.Perm (Fin M)
  let f (π τ : Permutations) (t : GiantTwoSidedResidueState P M) :=
    K (giantTwoSidedResiduePermute π s) (giantTwoSidedResiduePermute τ t)
  have hp : 0<Fintype.card Permutations := Fintype.card_pos_iff.mpr ⟨fun _ => Equiv.refl _⟩
  have hC : 0<((Fintype.card Permutations:ℝ)^2) := pow_pos (Nat.cast_pos.mpr hp) _
  have hs : (∑ t,∑ π : Permutations,∑ τ : Permutations,f π τ t)=∑ π,∑ τ,∑ t,f π τ t := by
    rw [sum_comm]
    exact sum_congr rfl fun π _ => sum_comm
  change (∑ t,(∑ π : Permutations,∑ τ : Permutations,f π τ t)/(Fintype.card Permutations:ℝ)^2)≤B
  rw [← sum_div,hs]
  apply (div_le_iff₀ hC).mpr
  calc
    _ ≤ ∑ _π : Permutations,∑ _τ : Permutations,B := by
      apply sum_le_sum
      intro π _
      apply sum_le_sum
      intro τ _
      have h := (giantTwoSidedResiduePermute (P:=P) τ).sum_comp (K (giantTwoSidedResiduePermute π s))
      exact h.trans_le (hK _)
    _ = _ := by simp only [sum_const,nsmul_eq_mul,card_univ]; ring

theorem giantTwoSidedResidueSlotAverage_column_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val] {M : ℕ}
    (K : GiantTwoSidedResidueState P M → GiantTwoSidedResidueState P M → ℝ)
    {B : ℝ} (hK : ∀ t,∑ s,K s t≤B) (t : GiantTwoSidedResidueState P M) :
    (∑ s,giantTwoSidedResidueSlotAverage K s t)≤B := by
  have hs (s : GiantTwoSidedResidueState P M) :
      giantTwoSidedResidueSlotAverage K s t=giantTwoSidedResidueSlotAverage (fun v u => K u v) t s := by
    unfold giantTwoSidedResidueSlotAverage
    dsimp only
    rw [sum_comm]
  simp_rw [hs]
  exact giantTwoSidedResidueSlotAverage_row_le (fun v u => K u v) hK t

theorem giantCandidateResiduePattern_absolute_rows_columns_eventually (ell m₀ : ℕ)
    {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      ∀ (k : ℕ) (C : S → Finset (Fin k)),(∀ i,(C i).card ≤ m₀) →
      ∀ (step : ℤ) (ζ : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell) (K₀ : ℝ),
        0≤K₀ → (∀ b c a,‖K b c a‖≤K₀) →
        (∀ s : GiantTwoSidedResidueState P (k+ell),
          (∑ t : GiantTwoSidedResidueState P (k+ell),giantTwoSidedResidueSlotAverage
            (giantTwoSidedResiduePatternAbsoluteEntry step q ζ K) s t)≤K₀*(Real.log x)^A) ∧
        (∀ t : GiantTwoSidedResidueState P (k+ell),
          (∑ s : GiantTwoSidedResidueState P (k+ell),giantTwoSidedResidueSlotAverage
            (giantTwoSidedResiduePatternAbsoluteEntry step q ζ K) s t)≤K₀*(Real.log x)^A) := by
  let v := Real.log 2/2
  have hv : 0<v := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨B,hB,hslot⟩ := exists_giantTwoSidedPattern_slot_bound hq hq1 hv (ell+m₀)
  let A := giantCandidateGroupLogRate*Real.log B
  refine ⟨A,mul_nonneg (by unfold giantCandidateGroupLogRate; positivity) (Real.log_nonneg hB),?_⟩
  filter_upwards [giantCandidateSelectedGroups_geometry_eventually,giantCandidateFullPrimes_prime_upper_eventually,
    giantCandidateSelectedGroups_exponential_cost_eventually B hB] with x hgeo hprime hcost
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro k C hC step ζ K K₀ hK₀ hK
  have hP (i : S) (p : ℕ) (hp : p∈P i) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)).1
  have hV (i : S) : 0<bandReciprocalMass (P i) := hv.trans ((hgeo S).2.1 i).1
  have hbudget (i : S) (z : ℕ) :
      (bandReciprocalMass (P i))⁻¹^(ell+(C i).card)*
      ((z:ℝ)+((ell+(C i).card:ℕ):ℝ))^(ell+(C i).card)*q^((z:ℝ)/2)≤B :=
    hslot _ _ _ ((hgeo S).2.1 i).1.le (Nat.add_le_add_left (hC i) _)
  have hBpow : B^Fintype.card S≤(Real.log x)^A := by rw [Fintype.card_coe]; exact hcost S
  have hrow (step : ℤ) (K : GiantTwoSidedPatternCoefficient P C ell)
      (hK : ∀ b c a,‖K b c a‖≤K₀) (s : GiantTwoSidedResidueState P (k+ell)) :
      giantTwoSidedResiduePatternAbsoluteRow step q ζ K s≤K₀*(Real.log x)^A :=
    (giantTwoSidedResiduePatternAbsoluteRow_le hP (hgeo S).1 hV step hq hq1.le
      (zero_le_one.trans hB) hK₀ ζ K hK hbudget s).trans (mul_le_mul_of_nonneg_left hBpow hK₀)
  constructor
  · intro s
    apply giantTwoSidedResidueSlotAverage_row_le
    intro u
    simp only [giantTwoSidedResiduePatternAbsoluteEntry]
    rw [sum_comm]
    exact hrow step K hK u
  · intro t
    apply giantTwoSidedResidueSlotAverage_column_le
    intro u
    simp only [giantTwoSidedResiduePatternAbsoluteEntry]
    rw [sum_comm]
    change giantTwoSidedResiduePatternAbsoluteColumn step q ζ K u≤K₀*(Real.log x)^A
    rw [giantTwoSidedResiduePatternAbsoluteColumn_eq_reverse hP hV step hq.le ζ K]
    exact hrow (-step) (fun b c a => K c b a) (fun b c a => hK c b a) u

theorem giantCandidateResiduePatternFamily_absolute_rows_columns_eventually {I : Type*} (ell m₀ : ℕ)
    {q : ℝ} (hq : 0<q) (hq1 : q<1) (C₁ : ℝ) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      ∀ (k : ℕ) (patterns : Finset I) (C : I → S → Finset (Fin k)),
        (∀ ν∈patterns,∀ i,(C ν i).card ≤ m₀) →
      ∀ (step : ℤ) (ζ : ℝ) (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell) (K₀ : I → ℝ),
        (∀ ν∈patterns,0≤K₀ ν ∧ ∀ b c a,‖K ν b c a‖≤K₀ ν) →
        (∑ ν∈patterns,K₀ ν)≤(Real.log x)^C₁ →
        (∀ s : GiantTwoSidedResidueState P (k+ell),
          (∑ t : GiantTwoSidedResidueState P (k+ell),∑ ν∈patterns,giantTwoSidedResidueSlotAverage
            (giantTwoSidedResiduePatternAbsoluteEntry step q ζ (K ν)) s t)≤(Real.log x)^(C₁+A)) ∧
        (∀ t : GiantTwoSidedResidueState P (k+ell),
          (∑ s : GiantTwoSidedResidueState P (k+ell),∑ ν∈patterns,giantTwoSidedResidueSlotAverage
            (giantTwoSidedResiduePatternAbsoluteEntry step q ζ (K ν)) s t)≤(Real.log x)^(C₁+A)) := by
  obtain ⟨A,hA,h⟩ := giantCandidateResiduePattern_absolute_rows_columns_eventually ell m₀ hq hq1
  refine ⟨A,hA,?_⟩
  filter_upwards [h,Real.tendsto_log_atTop.eventually_gt_atTop (0:ℝ)] with x hx hL
  intro S
  dsimp only
  intro nz
  let P (i : S) := giantCandidateGroup x i.val
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro k patterns C hC step ζ K K₀ hK hmass
  have hsum : (∑ ν∈patterns,K₀ ν*(Real.log x)^A)≤(Real.log x)^(C₁+A) := by
    rw [← sum_mul,Real.rpow_add hL]
    exact mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hL.le _)
  constructor
  · intro s
    rw [sum_comm]
    exact (sum_le_sum fun ν hν => (hx S nz k (C ν) (hC ν hν) step ζ (K ν) (K₀ ν)
      (hK ν hν).1 (hK ν hν).2).1 s).trans hsum
  · intro t
    rw [sum_comm]
    exact (sum_le_sum fun ν hν => (hx S nz k (C ν) (hC ν hν) step ζ (K ν) (K₀ ν)
      (hK ν hν).1 (hK ν hν).2).2 t).trans hsum

end
end ArtinMatthews
