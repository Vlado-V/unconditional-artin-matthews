module

public import ArtinMatthews.GiantSinglePrimeInterval
public import ArtinMatthews.GiantTwoSidedResiduePrimeFactor
public import ArtinMatthews.GiantTwoSidedResidueRootSum


set_option backward.privateInPublic true
@[expose] public section

/-!
# The literal full-prime residue average

Actual marking slots determine the active set of each numeric prime.
Finite residue summation factors the full average into the single-prime
expectations, including repeated labels among the marking slots.
-/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Actual visits at which a numeric prime occurs among the marking slots. -/
def giantSignedActualActiveVisits {J : Type*} [Fintype J] {PB : J → Finset ℕ}
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M) (p : ℕ) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => p ∈ markedPhysicalActivePrimes (labels i))

theorem mem_giantSignedActualActiveVisits {J : Type*} [Fintype J] {PB : J → Finset ℕ}
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M) (p : ℕ)
    (i : Fin (n + 1)) :
    i ∈ giantSignedActualActiveVisits labels p ↔ ∃ g k, (labels i g k).val = p := by
  simp only [giantSignedActualActiveVisits, Finset.mem_filter, Finset.mem_univ, true_and,
    markedPhysicalActivePrimes, markedPhysicalLabelSet, Finset.mem_biUnion,
    Finset.mem_image]

/-- Every actual slot satisfies its translated residue equation. -/
def GiantSignedFullPrimeActive {J : Type*} [Fintype J] {PB : J → Finset ℕ}
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (root : GiantTwoSidedFullResidue PB) : Prop :=
  ∀ i g k, root (giantTwoSidedResidueIndex g (labels i g k)) +
    (offset i : ZMod (giantTwoSidedResidueIndex g (labels i g k)).val) = 0

/-- The product over each visit's genuinely inactive numeric primes. -/
def giantSignedFullPrimeInactiveWeight {J : Type*} [Fintype J] {PB : J → Finset ℕ}
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ)
    (root : GiantTwoSidedFullResidue PB) : ℝ :=
  ∏ i, ∏ p ∈ (Finset.univ : Finset ↥(markedPhysicalBandPrimes PB)).filter
      (fun p => p.val ∉ markedPhysicalActivePrimes (labels i)),
    (1 - (1 - q i) * giantSignedPrimeResidueHit p.val offset i (root p))

def giantSignedFullPrimeResidueFactor {J : Type*} [Fintype J] {PB : J → Finset ℕ}
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ)
    (root : GiantTwoSidedFullResidue PB) : ℝ :=
  (if GiantSignedFullPrimeActive labels offset root then 1 else 0) *
    giantSignedFullPrimeInactiveWeight labels offset q root

/-- Uniform averaging on the actual full prime-residue tuple. -/
def giantSignedFullPrimeResidueMean {J : Type*} [Fintype J] {PB : J → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val] {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ) : ℝ :=
  (∑ root : GiantTwoSidedFullResidue PB, giantSignedFullPrimeResidueFactor labels offset q root) /
    ∏ p : ↥(markedPhysicalBandPrimes PB), (p.val : ℝ)

theorem giantSignedFullPrimeActive_iff {J : Type*} [Fintype J] {PB : J → Finset ℕ}
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (root : GiantTwoSidedFullResidue PB) :
    GiantSignedFullPrimeActive labels offset root ↔
      ∀ p : ↥(markedPhysicalBandPrimes PB),
        ∀ i ∈ giantSignedActualActiveVisits labels p.val,
          root p + (offset i : ZMod p.val) = 0 := by
  constructor
  · intro hall p i hi
    obtain ⟨g, k, hval⟩ := (mem_giantSignedActualActiveVisits labels p.val i).mp hi
    have hind : giantTwoSidedResidueIndex g (labels i g k) = p := Subtype.ext hval
    subst p
    exact hall i g k
  · intro hall i g k
    apply hall (giantTwoSidedResidueIndex g (labels i g k)) i
    exact (mem_giantSignedActualActiveVisits labels _ i).mpr ⟨g, k, rfl⟩

theorem giantSignedFullPrimeInactiveWeight_product {J : Type*} [Fintype J]
    {PB : J → Finset ℕ} {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ)
    (root : GiantTwoSidedFullResidue PB) :
    giantSignedFullPrimeInactiveWeight labels offset q root =
      ∏ p : ↥(markedPhysicalBandPrimes PB), ∏ i ∈ Finset.univ \ giantSignedActualActiveVisits labels p.val,
        (1 - (1 - q i) * giantSignedPrimeResidueHit p.val offset i (root p)) := by
  unfold giantSignedFullPrimeInactiveWeight
  simp_rw [Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp [giantSignedActualActiveVisits]

theorem giantSignedFullPrimeResidueFactor_product {J : Type*} [Fintype J]
    {PB : J → Finset ℕ} {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ)
    (root : GiantTwoSidedFullResidue PB) :
    giantSignedFullPrimeResidueFactor labels offset q root =
      ∏ p : ↥(markedPhysicalBandPrimes PB),
        (if ∀ i ∈ giantSignedActualActiveVisits labels p.val,
          root p + (offset i : ZMod p.val) = 0 then 1 else 0) *
        ∏ i ∈ Finset.univ \ giantSignedActualActiveVisits labels p.val,
          (1 - (1 - q i) * giantSignedPrimeResidueHit p.val offset i (root p)) := by
  have hindicator : (if GiantSignedFullPrimeActive labels offset root then (1 : ℝ) else 0) =
      ∏ p : ↥(markedPhysicalBandPrimes PB),
        if ∀ i ∈ giantSignedActualActiveVisits labels p.val,
          root p + (offset i : ZMod p.val) = 0 then 1 else 0 := by
    by_cases ha : GiantSignedFullPrimeActive labels offset root
    · have hall := (giantSignedFullPrimeActive_iff labels offset root).mp ha
      rw [ite_eq_left ha]
      symm
      exact Finset.prod_eq_one (fun p _ => ite_eq_left (hall p))
    · have hnot : ¬∀ p : ↥(markedPhysicalBandPrimes PB),
          ∀ i ∈ giantSignedActualActiveVisits labels p.val,
            root p + (offset i : ZMod p.val) = 0 :=
        fun hall => ha ((giantSignedFullPrimeActive_iff labels offset root).mpr hall)
      obtain ⟨p, hp⟩ := not_forall.mp hnot
      rw [ite_eq_right ha]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ p) (ite_eq_right hp)
  unfold giantSignedFullPrimeResidueFactor
  rw [hindicator, giantSignedFullPrimeInactiveWeight_product, Finset.prod_mul_distrib]

/-- The full tuple average factors by finite summation, with its actual
reciprocal prime cardinalities. -/
theorem giantSignedFullPrimeResidueMean_product {J : Type*} [Fintype J]
    {PB : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val] {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ) :
    giantSignedFullPrimeResidueMean labels offset q =
      ∏ p : ↥(markedPhysicalBandPrimes PB),
        giantSignedPrimeResidueExpectation p.val offset q (giantSignedActualActiveVisits labels p.val) := by
  unfold giantSignedFullPrimeResidueMean
  simp_rw [giantSignedFullPrimeResidueFactor_product]
  rw [← Fintype.prod_sum (fun (p : ↥(markedPhysicalBandPrimes PB)) (r : ZMod p.val) =>
    (if ∀ i ∈ giantSignedActualActiveVisits labels p.val,
      r + (offset i : ZMod p.val) = 0 then (1 : ℝ) else 0) *
      ∏ i ∈ Finset.univ \ giantSignedActualActiveVisits labels p.val,
        (1 - (1 - q i) * giantSignedPrimeResidueHit p.val offset i r))]
  simp only [giantSignedPrimeResidueExpectation, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, div_eq_mul_inv, Finset.prod_const_one]
  ring

end
end ArtinMatthews
