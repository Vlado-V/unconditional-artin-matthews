module

public import ArtinMatthews.MarkedMajorLabelSplit
public import ArtinMatthews.MarkedTypeIISharedLabels


set_option backward.privateInPublic true
@[expose] public section

/-! The actual shared unshared-label pairs in a dyadic factor. An equal
prime in any band is equivalent to a common divisor of the label products. -/
namespace ArtinMatthews
noncomputable section
open Finset
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] (P : J → Finset ℕ)
  (hP : ∀ j p, p ∈ P j → p.Prime)

include hP in
theorem markedMajorLabelPair_not_coprime_iff {b a : ℕ}
    (hb : b ∈ markedMajorLabelSet P) :
    ¬ b.Coprime a ↔ ∃ p ∈ Finset.univ.biUnion P, p ∣ b ∧ p ∣ a := by
  constructor
  · intro h
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show b.gcd a ≠ 1 from h)
    have hpb := hd.trans (Nat.gcd_dvd_left b a)
    obtain ⟨t,_,ht⟩ := mem_image.mp hb
    have hdT : p ∣ markedPrimeBandProduct P t := by rwa [ht]
    obtain ⟨j,hj⟩ := marked_prime_dvd_tuple_product hp (fun j => (t j:ℕ))
      (fun j => hP j _ (t j).2) hdT
    have hpP : p ∈ P j := hj.symm ▸ (t j).2
    exact ⟨p,mem_biUnion.mpr ⟨j,mem_univ _,hpP⟩,hpb,hd.trans (Nat.gcd_dvd_right b a)⟩
  · rintro ⟨p,hp,hpb,hpa⟩ hcop
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
    have h := Nat.dvd_gcd hpb hpa
    change b.gcd a = 1 at hcop
    rw [hcop] at h
    exact (hP j p hj).ne_one (Nat.dvd_one.mp h)

include hP in
theorem markedPrimeBandProduct_coprime_iff
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (b a : (j : J) → ↥(P j)) :
    (markedPrimeBandProduct P b).Coprime (markedPrimeBandProduct P a) ↔
      ∀ j, b j ≠ a j := by
  constructor
  · intro h j hj
    have hd₁ : (b j:ℕ) ∣ markedPrimeBandProduct P b := dvd_prod_of_mem _ (mem_univ j)
    have hd₂ : (b j:ℕ) ∣ markedPrimeBandProduct P a := by
      rw [hj]
      exact dvd_prod_of_mem _ (mem_univ j)
    have hd := Nat.dvd_gcd hd₁ hd₂
    change (markedPrimeBandProduct P b).gcd (markedPrimeBandProduct P a)=1 at h
    rw [h] at hd
    exact (hP j _ (b j).2).ne_one (Nat.dvd_one.mp hd)
  · intro h
    by_contra hc
    have hb : markedPrimeBandProduct P b ∈ markedMajorLabelSet P :=
      mem_image.mpr ⟨b,mem_univ _,rfl⟩
    obtain ⟨p,hp,hpb,hpa⟩ := (markedMajorLabelPair_not_coprime_iff P hP hb).mp hc
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
    obtain ⟨j,hj⟩ := marked_prime_dvd_tuple_product (hP i p hi) (fun j => (b j:ℕ))
      (fun j => hP j _ (b j).2) hpb
    obtain ⟨k,hk⟩ := marked_prime_dvd_tuple_product (hP i p hi) (fun k => (a k:ℕ))
      (fun k => hP k _ (a k).2) hpa
    have he : (b j:ℕ) = (a k:ℕ) := hj.symm.trans hk
    have hjk : j=k := by
      by_contra hne
      exact disjoint_left.mp (hdis hne) (b j).2 (he.symm ▸ (a k).2)
    subst k
    exact h j (Subtype.ext he)

def markedTypeIIDyadLabels (Y : ℝ) : Finset ℕ :=
  (markedMajorLabelSet P).filter (fun b => Y ≤ (b:ℝ) ∧ (b:ℝ) ≤ 4*Y)

theorem markedTypeIIDyadLabels_subset (Y : ℝ) (hY : 0 < Y) :
    markedTypeIIDyadLabels P Y ⊆ Ioc 0 ⌊4*Y⌋₊ := by
  intro b hb
  have hb' := (mem_filter.mp hb).2
  exact mem_Ioc.mpr ⟨by exact_mod_cast hY.trans_le hb'.1,
    (Nat.le_floor_iff (by positivity : 0 ≤ 4*Y)).mpr hb'.2⟩

theorem markedTypeIIDyadLabels_card_le (Y : ℝ) (hY : 0 < Y) :
    ((markedTypeIIDyadLabels P Y).card:ℝ) ≤ 4*Y := by
  apply le_trans (Nat.cast_le.mpr (card_le_card (markedTypeIIDyadLabels_subset P Y hY)))
  simpa only [Nat.card_Ioc, Nat.sub_zero] using (Nat.floor_le (by positivity : 0 ≤ 4*Y))

include hP in
theorem markedTypeIISharedDyadLabels_card_le (Y : ℝ) (hY : 0 < Y) :
    ((((markedTypeIIDyadLabels P Y)×ˢ(markedTypeIIDyadLabels P Y)).filter
      (fun z => ¬ z.1.Coprime z.2)).card:ℝ) ≤
      (4*Y)^2 * ∑ p ∈ Finset.univ.biUnion P, 1/(p:ℝ)^2 := by
  have hs : ((markedTypeIIDyadLabels P Y)×ˢ(markedTypeIIDyadLabels P Y)).filter
      (fun z => ¬ z.1.Coprime z.2) ⊆
        markedSharedPrimePairs (Finset.univ.biUnion P) ⌊4*Y⌋₊ := by
    intro z hz
    obtain ⟨hpair,hn⟩ := mem_filter.mp hz
    obtain ⟨hb,ha⟩ := mem_product.mp hpair
    obtain ⟨hbp,hbmax⟩ := mem_Ioc.mp (markedTypeIIDyadLabels_subset P Y hY hb)
    obtain ⟨hap,hamax⟩ := mem_Ioc.mp (markedTypeIIDyadLabels_subset P Y hY ha)
    exact (mem_markedSharedPrimePairs _ _ _ _).mpr
      ⟨hbp,hbmax,hap,hamax,(markedMajorLabelPair_not_coprime_iff P hP (mem_filter.mp hb).1).mp hn⟩
  calc
    _ ≤ ((markedSharedPrimePairs (Finset.univ.biUnion P) ⌊4*Y⌋₊).card:ℝ) := Nat.cast_le.mpr (card_le_card hs)
    _ ≤ (⌊4*Y⌋₊:ℝ)^2 * ∑ p ∈ Finset.univ.biUnion P, 1/(p:ℝ)^2 :=
      markedSharedPrimePairs_real_card_le _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) 2)
      (sum_nonneg fun _ _ => by positivity)

end
end ArtinMatthews
