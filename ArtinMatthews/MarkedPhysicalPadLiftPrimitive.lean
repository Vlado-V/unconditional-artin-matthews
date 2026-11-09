module

public import ArtinMatthews.MarkedPhysicalPadCofactorTerm
public import ArtinMatthews.MarkedPhysicalEndpointPrimitive
public import ArtinMatthews.MarkedMinorArcPrimeProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Automatic primitivity of both literal lifted endpoints on the
small-determinant support. The proof uses a genuinely unshared band
prime; repeated/forbidden pads and coincident last labels remain separate. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {P : J → Finset ℕ}
  (hP : ∀ j p,p ∈ P j → p.Prime)
  (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
  (b a : (j : J) → ↥(P j))

include hP hdis

theorem markedPhysicalLastLabel_not_dvd (hne : ∀ j,b j ≠ a j) (j : J) :
    ¬(b j:ℕ) ∣ markedPrimeBandProduct P a := by
  intro hd
  obtain ⟨k,hjk⟩ := marked_prime_dvd_tuple_product (hP j _ (b j).2)
    (fun k => (a k:ℕ)) (fun k => hP k _ (a k).2) hd
  have he : j=k := by
    by_contra hne'
    exact Finset.disjoint_left.mp (hdis hne') (b j).2 (hjk.symm ▸ (a k).2)
  subst k
  exact hne j (Subtype.ext hjk)

theorem markedPhysicalLastProduct_coprime_iff :
    (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a) ↔ ∀ j,b j ≠ a j := by
  constructor
  · intro hc j hj
    have hpb : (b j:ℕ) ∣ markedPrimeBandProduct P b :=
      Finset.dvd_prod_of_mem (fun k => (b k:ℕ)) (Finset.mem_univ j)
    have hpa : (b j:ℕ) ∣ markedPrimeBandProduct P a := by
      rw [hj]
      exact Finset.dvd_prod_of_mem (fun k => (a k:ℕ)) (Finset.mem_univ j)
    exact (hP j _ (b j).2).not_dvd_one (by
      simpa only [hc.gcd_eq_one] using Nat.dvd_gcd hpb hpa)
  · intro hj
    apply Nat.Coprime.prod_left
    intro j _
    exact (hP j _ (b j).2).coprime_iff_not_dvd.mpr (markedPhysicalLastLabel_not_dvd hP hdis b a hj j)

theorem markedPhysicalPad_lifts_coprime [Nonempty J]
    {pads : ℕ} (c : MarkedPhysicalMarking P pads) {m s r n : ℕ} {W : ℝ}
    (hbelow : ∀ j p,p ∈ P j → (p:ℝ)<W) (hne : ∀ j,b j ≠ a j)
    (hm : MarkedPhysicalBandRough P m) (hr : MarkedPhysicalBandRough P r)
    (hs : ∀ p : ℕ,p.Prime → p ∣ s → W ≤ (p:ℝ))
    (hn : ∀ p : ℕ,p.Prime → p ∣ n → W ≤ (p:ℝ))
    (ht : |((markedPrimeBandProduct P b:ℤ)*m*n-(markedPrimeBandProduct P a:ℤ)*r*s:ℤ)| < W) :
    (markedPhysicalMarkingProduct c*markedPrimeBandProduct P b*m).Coprime s ∧
      (markedPhysicalMarkingProduct c*markedPrimeBandProduct P a*r).Coprime n := by
  let j : J := Classical.choice inferInstance
  have hsr := markedPhysicalBandRough_of_rough P hP hbelow hs
  have hnr := markedPhysicalBandRough_of_rough P hP hbelow hn
  have hBs := markedPhysicalMarkingProduct_coprime hP
    ((markedPhysicalMarkingSplit pads).symm (c,b)) hsr
  have hAn := markedPhysicalMarkingProduct_coprime hP
    ((markedPhysicalMarkingSplit pads).symm (c,a)) hnr
  rw [markedPhysicalPad_append_product P hP pads c b] at hBs
  rw [markedPhysicalPad_append_product P hP pads c a] at hAn
  have htn : |((markedPrimeBandProduct P a:ℤ)*r*s-(markedPrimeBandProduct P b:ℤ)*m*n:ℤ)| < W := by
    rw [← abs_sub_comm]
    exact ht
  have hpb : (b j:ℕ) ∣ markedPrimeBandProduct P b :=
    Finset.dvd_prod_of_mem (fun k => (b k:ℕ)) (Finset.mem_univ j)
  have hpa : (a j:ℕ) ∣ markedPrimeBandProduct P a :=
    Finset.dvd_prod_of_mem (fun k => (a k:ℕ)) (Finset.mem_univ j)
  exact ⟨markedPhysical_lift_primitive hs hBs ht (hP j _ (b j).2) hpb
      (markedPhysicalLastLabel_not_dvd hP hdis b a hne j) (hr j _ (b j).2) (hsr j _ (b j).2),
    markedPhysical_lift_primitive hn hAn htn (hP j _ (a j).2) hpa
      (markedPhysicalLastLabel_not_dvd hP hdis a b (fun k => (hne k).symm) j)
      (hm j _ (a j).2) (hnr j _ (a j).2)⟩

end
end ArtinMatthews
