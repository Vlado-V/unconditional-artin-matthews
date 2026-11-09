module

public import ArtinMatthews.GiantSignedUnboundedClean


set_option backward.privateInPublic true
@[expose] public section

/-! Exact disintegration of the original ordered-memory counting sum. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

def giantSignedMemoryFiberEquiv {B : Type*} (P : B → Finset ℕ) :
    GiantSignedMemory P ≃ Σ s : GiantSignedMemorySectors P, GiantSignedResidues s.2 where
  toFun m := ⟨⟨m.1, (giantSignedMemoryCoordinates P m).2.1⟩,
    (giantSignedMemoryCoordinates P m).2.2⟩
  invFun m := giantSignedMemoryAt m.1 m.2
  left_inv m := by
    apply Sigma.ext rfl
    apply heq_of_eq
    funext g i
    exact Sigma.eta _
  right_inv m := by rcases m with ⟨⟨degree, primes⟩, residues⟩; rfl

theorem giantSignedMemory_tsum {B : Type*} [Fintype B] {P : B → Finset ℕ}
    [∀ (g : B) (p : P g), NeZero p.val] (f : GiantSignedMemory P → ℝ≥0∞) :
    (∑' m, f m) = ∑' s : GiantSignedMemorySectors P,
      ∑ r : GiantSignedResidues s.2, f (giantSignedMemoryAt s r) := by
  classical
  calc
    _ = ∑' m, f ((giantSignedMemoryFiberEquiv P).symm m) :=
      ((giantSignedMemoryFiberEquiv P).symm.tsum_eq f).symm
    _ = ∑' s : GiantSignedMemorySectors P, ∑' r : GiantSignedResidues s.2,
        f (giantSignedMemoryAt s r) := ENNReal.tsum_sigma' _
    _ = _ := by simp only [tsum_fintype]

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val]

instance giantSignedSmallResidue_fintype : Fintype (GiantTwoSidedFullResidue PS) := by
  classical
  letI : ∀ p : ↥(markedPhysicalBandPrimes PS), Fintype (ZMod p.val) := fun p => by
    let : NeZero p.val := ‹∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val› p
    infer_instance
  change Fintype ((p : ↥(markedPhysicalBandPrimes PS)) → ZMod p.val)
  infer_instance

def giantSignedAmbientEnergy {M : ℕ} (ν : ∀ g, PB g → ℝ)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB M → GiantSignedMemory PB → ℂ) :
    ℝ≥0∞ :=
  ∑' m : GiantSignedMemory PB, ∑ y : GiantTwoSidedFullResidue PS,
    ∑ a : MarkedPhysicalMarking PB M,
      ENNReal.ofReal (giantSignedSmallHaar PS * giantSignedMemoryMass ν m *
        giantSignedActiveMass ν a * ‖f y a m‖ ^ 2)

def giantSignedAmbientToSectors {M : ℕ}
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB M → GiantSignedMemory PB → ℂ) :
    GiantSignedSectorFunctions PS (PB := PB) M :=
  fun s x a => f x.1 a (giantSignedMemoryAt s x.2)

theorem giantSignedAmbientEnergy_disintegrate {M : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f : GiantTwoSidedFullResidue PS → MarkedPhysicalMarking PB M → GiantSignedMemory PB → ℂ) :
    giantSignedAmbientEnergy PS ν f =
      giantSignedSectorEnergy PS ν (giantSignedAmbientToSectors PS f) := by
  classical
  unfold giantSignedAmbientEnergy
  rw [giantSignedMemory_tsum]
  unfold giantSignedSectorEnergy
  apply tsum_congr
  intro s
  simp only [giantSignedMemoryAt_mass]
  have hmass : 0 ≤ giantSignedSmallHaar PS * giantSignedPrimeListMass ν s.2 := by
    apply mul_nonneg (giantSignedSmallHaar_nonneg PS)
    exact giantSignedMemoryMass_nonneg ν hν (giantSignedMemoryAt s 0)
  have hactive (a : MarkedPhysicalMarking PB M) : 0 ≤ giantSignedActiveMass ν a :=
    Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g (a g i)
  unfold giantSignedAmbientToSectors
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  simp only [← mul_assoc]
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun a _ =>
      mul_nonneg (mul_nonneg hmass (hactive a)) (sq_nonneg _))]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
    Finset.sum_nonneg fun a _ => mul_nonneg (mul_nonneg hmass (hactive a)) (sq_nonneg _))]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun a _ =>
    mul_nonneg (mul_nonneg hmass (hactive a)) (sq_nonneg _))]
  rw [Finset.sum_comm]

end
end ArtinMatthews
