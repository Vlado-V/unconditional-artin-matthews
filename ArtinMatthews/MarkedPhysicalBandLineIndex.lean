module

public import ArtinMatthews.MarkedPhysicalFullBandLines


set_option backward.privateInPublic true
@[expose] public section

/-! The common full-band line tuple uses exactly the physical marking
addresses and the raw active-visit sets. No distinctness or independence
assumption is needed for this finite indexing identity. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalBandPrime_mem {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (p : ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j)))) :
    (p.1:ℕ) ∈ markedPhysicalBandPrimes P := by
  obtain ⟨j,hj,hp⟩ := Finset.mem_biUnion.mp p.2
  exact Finset.mem_biUnion.mpr ⟨j,hj,(mem_markedRawPrimeBand (P j) p.1).mp hp⟩

def markedPhysicalBandPrimeIndexEquiv {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) :
    ↥(markedPhysicalBandPrimes P) ≃ ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j))) where
  toFun p := markedPhysicalBandPrimeIndex hP p.1 p.2
  invFun p := ⟨(p.1:ℕ),markedPhysicalBandPrime_mem p⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedPhysicalBandLineHit_iff {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (ell : MarkedPhysicalBandLines P)
    (p : ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j))))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    markedPhysicalBandLineHit hP ell z hz (p.1:ℕ) ↔
      markedPrimePositionLine (p.1:ℕ) z hz = ell p := by
  simp only [markedPhysicalBandLineHit,dite_eq_left (markedPhysicalBandPrime_mem p)]
  rfl

def markedPhysicalMarkingPathRawSlots {J ι : Type*} {P : J → Finset ℕ} {M : ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (a : ι → MarkedPhysicalMarking P M) :
    ι → MarkedRawActive (fun j => markedRawPrimeBand (P j)) M :=
  fun v => (markedPhysicalMarkingEquiv P hP M).symm (a v)

theorem markedPhysicalMarkingPath_active_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (p : Nat.Primes) (v : Fin (N+1)) :
    (p:ℕ) ∈ markedPhysicalActivePrimes (a v) ↔
      v ∈ markedMemoryActiveVisits (markedPhysicalMarkingPathRawSlots hP a) p := by
  constructor
  · intro hp
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,j,k,?_⟩
    exact Subtype.ext hk
  · intro hv
    obtain ⟨j,k,hjk⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨k,Finset.mem_univ _,congrArg Subtype.val hjk⟩⟩

theorem markedPhysicalBandLinePrimePathFactor_inactive {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (ell : MarkedPhysicalBandLines P)
    (p : ↥(markedMemoryBandPrimeUnion (fun j => markedRawPrimeBand (P j)))) :
    markedPhysicalBandLinePrimePathFactor hP ell Finset.univ a (markedMemoryVisitQ q N) z hz (p.1:ℕ) =
      ∏ v ∈ Finset.univ \ markedMemoryActiveVisits (markedPhysicalMarkingPathRawSlots hP a) p.1,
        (1-markedMemoryEta q N v*markedLineHit (markedMemoryPositionLines p.1 z hz) v (ell p)) := by
  have hfactor (v : Fin (N+1)) :
      markedPhysicalBandLineVisitFactor hP ell (markedPhysicalActivePrimes (a v)) (markedMemoryVisitQ q N v)
          (z v) (hz v) (p.1:ℕ) =
        if v ∈ markedMemoryActiveVisits (markedPhysicalMarkingPathRawSlots hP a) p.1 then 1
        else (1-markedMemoryEta q N v*markedLineHit (markedMemoryPositionLines p.1 z hz) v (ell p)) := by
    unfold markedPhysicalBandLineVisitFactor
    simp only [markedPhysicalMarkingPath_active_iff hP a]
    simp only [markedPhysicalBandLineHit_iff hP ell p]
    by_cases ha : v ∈ markedMemoryActiveVisits (markedPhysicalMarkingPathRawSlots hP a) p.1
    · simp only [ha,ite_true]
    · simp only [ha,ite_false]
      by_cases hh : markedPrimePositionLine (p.1:ℕ) (z v) (hz v) = ell p
      · simp [markedMemoryPositionLines,markedLineHit,markedMemoryEta,hh]
      · simp [markedMemoryPositionLines,markedLineHit,hh,Ne.symm hh]
  unfold markedPhysicalBandLinePrimePathFactor
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  congr 1
  ext v
  simp

end ArtinMatthews
