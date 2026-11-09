module

public import ArtinMatthews.MarkedPhysicalBonferroniModulus
public import ArtinMatthews.MarkedPhysicalRootResidue


set_option backward.privateInPublic true
@[expose] public section

/-! Each performed Bonferroni monomial is a literal function of the
selected squarefree root residue. The actual projective hit equivalence
is used prime by prime; no averaging or independence is asserted. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalResiduePrimeHit {S : ℕ} (hS : Squarefree S)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (p : ℕ) : Prop :=
  if hp : p ∈ S.primeFactors then
    let _ : Fact p.Prime := ⟨(Nat.mem_primeFactors.mp hp).1⟩
    markedPrimePositionLine p z hz = markedRootKernelTuple hS g ⟨p,hp⟩
  else False

def markedPhysicalResidueVisitFactor {S : ℕ} (hS : Squarefree S)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (active : Finset ℕ) (r : ℝ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (p : ℕ) : ℝ :=
  if p ∈ active then 1 else if markedPhysicalResiduePrimeHit hS g z hz p then r else 1

def markedPhysicalResiduePrimePathFactor {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (hS : Squarefree S) (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : ℕ) : ℝ :=
  ∏ v ∈ I,markedPhysicalResidueVisitFactor hS g (markedPhysicalActivePrimes (a v)) (r v) (z v) (hz v) p

def markedPhysicalResiduePrimeLoss {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (hS : Squarefree S) (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : ℕ) : ℝ :=
  1-markedPhysicalResiduePrimePathFactor hS g I a r z hz p

def markedPhysicalResidueBonferroniMonomial {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (hS : Squarefree S) (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ) : ℝ :=
  (∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalResiduePrimePathFactor hS g I a r z hz p)*
    ∏ p ∈ T,markedPhysicalResiduePrimeLoss hS g I a r z hz p

theorem markedPhysicalRootLift_nat_hit_iff {S : ℕ} (hS : Squarefree S)
    (root completion : ℤ × ℤ) (hdet : markedMinorIntegerDet root completion=1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) (markedPhysicalRootMatrix root completion hdet)=g)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {p : ℕ} (hp : p ∈ S.primeFactors) :
    p ∣ (markedPhysicalRootLift root completion z).1.natAbs ↔ markedPhysicalResiduePrimeHit hS g z hz p := by
  have hn : p ∣ (markedPhysicalRootLift root completion z).1.natAbs ↔
      (p:ℤ) ∣ (markedPhysicalRootLift root completion z).1 := by
    constructor
    · intro h
      apply Int.natAbs_dvd_natAbs.mp
      simpa only [Int.natAbs_natCast] using h
    · intro h
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h
  simp only [markedPhysicalResiduePrimeHit,dite_eq_left hp]
  exact hn.trans (markedPhysicalRootLift_kernel_hit hS root completion hdet g hred ⟨p,hp⟩ z hz)

theorem markedPhysicalPrimePathFactor_eq_residue {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M S : ℕ} (hS : Squarefree S)
    (root completion : ℤ × ℤ) (hdet : markedMinorIntegerDet root completion=1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) (markedPhysicalRootMatrix root completion hdet)=g)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) {p : ℕ} (hp : p ∈ S.primeFactors) :
    markedPhysicalPrimePathFactor I a r (fun v => (markedPhysicalRootLift root completion (z v)).1.natAbs) p =
      markedPhysicalResiduePrimePathFactor hS g I a r z hz p := by
  unfold markedPhysicalPrimePathFactor markedPhysicalResiduePrimePathFactor
  apply Finset.prod_congr rfl
  intro v _
  unfold markedPhysicalPrimeVisitFactor markedPhysicalResidueVisitFactor
  simp only [markedPhysicalRootLift_nat_hit_iff hS root completion hdet g hred (z v) (hz v) hp]

theorem markedPhysicalBonferroniMonomial_eq_residue {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} {M S : ℕ} (hS : Squarefree S)
    (root completion : ℤ × ℤ) (hdet : markedMinorIntegerDet root completion=1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) (markedPhysicalRootMatrix root completion hdet)=g)
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ)
    (hused : markedPhysicalPathUsedPrimes I a ⊆ S.primeFactors) (hT : T ⊆ S.primeFactors) :
    markedPhysicalJointBonferroniMonomial I a r (fun v => (markedPhysicalRootLift root completion (z v)).1.natAbs) T =
      markedPhysicalResidueBonferroniMonomial hS g I a r z hz T := by
  unfold markedPhysicalJointBonferroniMonomial markedPhysicalUsedPrimeWeight markedPhysicalResidueBonferroniMonomial
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    exact markedPhysicalPrimePathFactor_eq_residue hS root completion hdet g hred I a r z hz (hused hp)
  · apply Finset.prod_congr rfl
    intro p hp
    unfold markedPhysicalInactivePrimeLoss markedPhysicalResiduePrimeLoss
    rw [markedPhysicalPrimePathFactor_eq_residue hS root completion hdet g hred I a r z hz (hT hp)]

theorem markedPhysicalBonferroniMonomial_eq_selected_residue {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes P) (root completion : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalBonferroniModulus I a T)))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (markedPhysicalBonferroniModulus I a T)))
      (markedPhysicalRootMatrix root completion hdet)=g) :
    markedPhysicalJointBonferroniMonomial I a r (fun v => (markedPhysicalRootLift root completion (z v)).1.natAbs) T =
      markedPhysicalResidueBonferroniMonomial (markedPhysicalBonferroniModulus_squarefree hP I a hT) g I a r z hz T := by
  exact markedPhysicalBonferroniMonomial_eq_residue _ root completion hdet g hred I a r z hz T
    (fun p hp => markedPhysicalBonferroniModulus_mem_primeFactors hP I a hT (Finset.mem_union_left T hp))
    (fun p hp => markedPhysicalBonferroniModulus_mem_primeFactors hP I a hT (Finset.mem_union_right _ hp))

end ArtinMatthews
