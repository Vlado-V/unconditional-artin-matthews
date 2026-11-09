module

public import ArtinMatthews.GiantTwoSidedEndpointStates
public import ArtinMatthews.MarkedPhysicalPadCollisionMass


set_option backward.privateInPublic true
@[expose] public section

/-! The shared prefix and its unshared final label are the literal
ordered physical lists. Their original state and target masses split
into the shared harmonic mass and two remaining label factors. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantTwoSidedSplit_distinct_iff {J : Type*} {P : J → Finset ℕ} {k : ℕ}
    (c : MarkedPhysicalMarking P k) (b : (j : J) → ↥(P j)) :
    MarkedPhysicalMarkingDistinct ((markedPhysicalMarkingSplit k).symm (c,b)) ↔
      MarkedPhysicalMarkingDistinct c ∧ ∀ j,b j ∉ Set.range (c j) := by
  change (∀ j,Function.Injective (Fin.snoc (c j) (b j))) ↔ _
  simp only [Fin.snoc_injective_iff,forall_and,MarkedPhysicalMarkingDistinct]

theorem giantTwoSidedSplit_divisibility_iff {J : Type*} {P : J → Finset ℕ} {k n : ℕ}
    (c : MarkedPhysicalMarking P k) (b : (j : J) → ↥(P j)) :
    (∀ j l, (((markedPhysicalMarkingSplit k).symm (c,b)) j l:ℕ) ∣ n) ↔
      (∀ j l, (c j l:ℕ) ∣ n) ∧ ∀ j, (b j:ℕ) ∣ n := by
  change (∀ j l,((Fin.snoc (α:=fun _ => ↥(P j)) (c j) (b j) l):ℕ) ∣ n) ↔ _
  constructor
  · intro h
    exact ⟨fun j l => by simpa only [Fin.snoc_castSucc] using h j l.castSucc,
      fun j => by simpa only [Fin.snoc_last] using h j (Fin.last k)⟩
  · rintro ⟨hc,hb⟩ j l
    refine Fin.lastCases ?_ (fun i => ?_) l
    · simpa only [Fin.snoc_last] using hb j
    · simpa only [Fin.snoc_castSucc] using hc j i

theorem giantTwoSidedShared_free_coprime {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) {k : ℕ}
    (c : MarkedPhysicalMarking P k) (j : J) (b : ↥(P j)) (hb : b ∉ Set.range (c j)) :
    (b:ℕ).Coprime (markedPhysicalMarkingProduct c) := by
  have hp := hP j b.val b.property
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  obtain ⟨i,l,he⟩ := (markedPhysicalMarkingProduct_prime_dvd_iff hP c hp).mp h
  have hji : j=i := by
    by_contra hn
    exact disjoint_left.mp (hdis hn) b.property (he.symm ▸ (c i l).property)
  subst i
  exact hb ⟨l,Subtype.ext he.symm⟩

theorem giantTwoSidedShared_free_dvd_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) {k : ℕ}
    (c : MarkedPhysicalMarking P k) (j : J) (b : ↥(P j)) (hb : b ∉ Set.range (c j))
    (w : ℕ) :
    (b:ℕ) ∣ markedPhysicalMarkingProduct c*w ↔ (b:ℕ) ∣ w :=
  (giantTwoSidedShared_free_coprime hP hdis c j b hb).dvd_mul_left

theorem giantTwoSidedShared_product_coprime {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k m : ℕ} (c : MarkedPhysicalMarking P k)
    (hm : ∀ j p,p∈P j → p.Coprime m) :
    (markedPhysicalMarkingProduct c).Coprime m := by
  apply Nat.Coprime.prod_left
  intro j _
  apply Nat.Coprime.prod_left
  intro l _
  exact hm j _ (c j l).property

theorem giantTwoSidedShared_mass_factor {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k : ℕ) (c : MarkedPhysicalMarking P k) :
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+1) *
      (∏ j,(bandReciprocalMass (P j))⁻¹) /
      (markedPhysicalMarkingProduct c:ℝ) =
      markedPhysicalPadHarmonicMass P k c * (∏ j,(bandReciprocalMass (P j))⁻¹)^2 := by
  let V (j : J) := bandReciprocalMass (P j)
  let B := ∏ j,(V j)⁻¹
  let D := (markedPhysicalMarkingProduct c:ℝ)
  have hm : markedPhysicalPadHarmonicMass P k c = markedPhysicalMass V k*(1/D) := by
    rw [← markedPhysicalReciprocalProduct_eq]
    exact (markedPhysicalMass_mul_reciprocal P k c).symm
  change markedPhysicalMass V (k+1)*B/D = markedPhysicalPadHarmonicMass P k c*B^2
  rw [← markedPhysicalMass_edge V k,hm]
  ring

end
end ArtinMatthews
