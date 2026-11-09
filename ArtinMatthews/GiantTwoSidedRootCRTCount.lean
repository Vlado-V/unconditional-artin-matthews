module

public import ArtinMatthews.GiantTwoSidedRootResidueSplit
public import ArtinMatthews.GiantTwoSidedRootClass
public import ArtinMatthews.ScalarWeightedBonferroni


set_option backward.privateInPublic true
@[expose] public section

/-! The original path-residue sum is exactly the weighted scalar CRT
count, with all deterministic active-prime factors retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedRootResidue_sum_eq_count {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ)
    (hc : GiantTwoSidedActiveCompatible univ labels offset) (lo hi : ℕ) :
    (∑ root∈Ico lo hi,giantTwoSidedRootResidueFactor P labels q offset (root:ℤ)) =
      giantTwoSidedActiveResidueWeight univ labels (markedMemoryVisitQ q n) offset *
        scalarWeightedResidueCountIco
          (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes univ labels)
          (giantTwoSidedResidueLossNat univ (markedMemoryVisitQ q n) offset)
          lo hi (giantTwoSidedActiveModulus labels) (giantTwoSidedRootClass hP labels offset) := by
  simp_rw [giantTwoSidedRootResidueFactor_forced hdis,
    giantTwoSidedActiveRoot_iff_class hP labels offset hc]
  unfold scalarWeightedResidueCountIco scalarWeightedResidueLoss
  rw [sum_filter,mul_sum]
  apply sum_congr rfl
  intro root _
  split_ifs <;> simp only [mul_zero]

theorem giantTwoSidedRootResidue_sum_incompatible {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ)
    (hc : ¬GiantTwoSidedActiveCompatible univ labels offset) (lo hi : ℕ) :
    (∑ root∈Ico lo hi,giantTwoSidedRootResidueFactor P labels q offset (root:ℤ))=0 := by
  apply sum_eq_zero
  intro root _
  rw [giantTwoSidedRootResidueFactor_active hdis,
    ite_eq_right (giantTwoSidedActiveRoot_impossible univ labels offset hc root)]

end
end ArtinMatthews
