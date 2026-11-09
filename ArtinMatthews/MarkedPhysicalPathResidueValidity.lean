module

public import ArtinMatthews.MarkedPhysicalBonferroniResidue
public import ArtinMatthews.MarkedPhysicalPathArrays


set_option backward.privateInPublic true
@[expose] public section

/-! Actual physical list validity is a finite residue incidence guard.
The performed modulus contains every active label by construction;
ordered-list distinctness is retained in the guard. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPhysicalResidueLabelValid {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M S : ℕ} (hS : Squarefree S)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) : Prop :=
  ∀ v∈I,MarkedPhysicalMarkingDistinct (a v) ∧
    ∀ j k,markedPhysicalResiduePrimeHit hS g (z v) (hz v) (a v j k:ℕ)

theorem markedPhysical_label_mem_pathUsed {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (v : ι) (hv : v∈I) (j : J) (k : Fin M) :
    (a v j k:ℕ)∈markedPhysicalPathUsedPrimes I a := by
  apply Finset.mem_biUnion.mpr
  refine ⟨v,hv,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,?_⟩⟩
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩

theorem markedPhysicalLiftedLabelValid_iff_residue {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M S : ℕ} (hS : Squarefree S)
    (root completion : ℤ × ℤ) (hdet : markedMinorIntegerDet root completion=1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S))
      (markedPhysicalRootMatrix root completion hdet)=g)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (hused : markedPhysicalPathUsedPrimes I a⊆S.primeFactors) :
    (∀ v∈I,MarkedPhysicalStateCondition (markedPhysicalRootLift root completion (z v)) (a v)) ↔
      markedPhysicalResidueLabelValid hS g I a z hz := by
  have hh (v : ι) (hv : v∈I) (j : J) (k : Fin M) :
      ((a v j k:ℕ):ℤ)∣(markedPhysicalRootLift root completion (z v)).1 ↔
        markedPhysicalResiduePrimeHit hS g (z v) (hz v) (a v j k:ℕ) := by
    have hn : ((a v j k:ℕ):ℤ)∣(markedPhysicalRootLift root completion (z v)).1 ↔
        (a v j k:ℕ)∣(markedPhysicalRootLift root completion (z v)).1.natAbs := by
      rw [← Int.natAbs_dvd_natAbs,Int.natAbs_natCast]
    exact hn.trans (markedPhysicalRootLift_nat_hit_iff hS root completion hdet g hred
      (z v) (hz v) (hused (markedPhysical_label_mem_pathUsed I a v hv j k)))
  constructor
  · intro h v hv
    exact ⟨(h v hv).2.1,fun j k => (hh v hv j k).mp ((h v hv).2.2 j k)⟩
  · intro h v hv
    exact ⟨(markedPhysicalRootLift_primitive_iff root completion (z v) hdet).mpr (hz v),
      (h v hv).1,fun j k => (hh v hv j k).mpr ((h v hv).2 j k)⟩

theorem markedPhysicalLiftedLabelValid_iff_selected_residue {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ)
    (hT : T⊆markedPhysicalBandPrimes P) (root completion : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalBonferroniModulus I a T)))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (markedPhysicalBonferroniModulus I a T)))
      (markedPhysicalRootMatrix root completion hdet)=g) :
    (∀ v∈I,MarkedPhysicalStateCondition (markedPhysicalRootLift root completion (z v)) (a v)) ↔
      markedPhysicalResidueLabelValid (markedPhysicalBonferroniModulus_squarefree hP I a hT) g I a z hz :=
  markedPhysicalLiftedLabelValid_iff_residue _ root completion hdet g hred I a z hz
    (fun _ hp => markedPhysicalBonferroniModulus_mem_primeFactors hP I a hT (Finset.mem_union_left T hp))

theorem markedPhysicalPathArrayValid_iff_selected_residue {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M n : ℕ} {Z : Finset (ℤ × ℤ)}
    (pos : MarkedPhysicalPositionPath Z n) (a : MarkedPhysicalLabelPath P M n)
    (z : Fin (n+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ)
    (hT : T⊆markedPhysicalBandPrimes P) (root completion : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalBonferroniModulus Finset.univ a T)))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (markedPhysicalBonferroniModulus Finset.univ a T)))
      (markedPhysicalRootMatrix root completion hdet)=g)
    (hpos : ∀ v,(pos v).1=markedPhysicalRootLift root completion (z v)) :
    MarkedPhysicalPathArrayValid pos a ↔
      markedPhysicalResidueLabelValid (markedPhysicalBonferroniModulus_squarefree hP Finset.univ a hT)
        g Finset.univ a z hz := by
  have h := markedPhysicalLiftedLabelValid_iff_selected_residue hP Finset.univ a z hz T hT
    root completion hdet g hred
  simpa only [MarkedPhysicalPathArrayValid,Finset.mem_univ,forall_const,← hpos] using h

end
end ArtinMatthews
