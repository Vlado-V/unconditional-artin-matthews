module

public import ArtinMatthews.GiantTwoSidedActiveClass
public import ArtinMatthews.GiantTwoSidedActiveModulus


set_option backward.privateInPublic true
@[expose] public section

/-! The concrete active modulus and canonical root residue use the
same distinct-prime set. Compatibility is tested on the actual label
path; an incompatible path has no contribution from any Nat root. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem giantTwoSidedPathUsed_prime {J ι : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (I : Finset ι) (labels : ι → MarkedPhysicalMarking P M) :
    ∀ p∈markedPhysicalPathUsedPrimes I labels,p.Prime := by
  intro p hp
  obtain ⟨j,_,hj⟩ := mem_biUnion.mp (markedPhysicalPathUsedPrimes_subset I labels hp)
  exact hP j p hj

def giantTwoSidedRootClass {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (offset : Fin (n+1) → ℤ) : ℕ :=
  giantTwoSidedCRTResidue (markedPhysicalPathUsedPrimes univ labels)
    (giantTwoSidedPathUsed_prime hP univ labels) (giantTwoSidedActiveResidue univ labels offset)

theorem giantTwoSidedActiveRoot_iff_class {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (offset : Fin (n+1) → ℤ)
    (hc : GiantTwoSidedActiveCompatible univ labels offset) (root : ℕ) :
    GiantTwoSidedActiveRoot univ labels offset root ↔
      Nat.ModEq (giantTwoSidedActiveModulus labels) root (giantTwoSidedRootClass hP labels offset) := by
  rw [giantTwoSidedActiveRoot_iff_residues univ labels offset hc]
  exact (giantTwoSidedCRTResidue_iff (markedPhysicalPathUsedPrimes univ labels)
    (giantTwoSidedPathUsed_prime hP univ labels) (giantTwoSidedActiveResidue univ labels offset) root).symm

end
end ArtinMatthews
