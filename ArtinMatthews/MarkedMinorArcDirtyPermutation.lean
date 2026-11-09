module

public import ArtinMatthews.MarkedMinorArcDirtyOmission
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fintype.Perm


set_option backward.privateInPublic true
@[expose] public section

/-! The actual uniform permutation symmetrization produces the omission factor M^(-K). -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedPermutation_slot_probability (n : ℕ) (slot target : Fin (n+1)) :
    (∑ σ : Equiv.Perm (Fin (n+1)),
      if σ slot = target then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0) =
      1/(n+1:ℝ) := by
  classical
  have hslot := Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0:Fin (n+1)) slot))
    (fun σ : Equiv.Perm (Fin (n+1)) =>
      if σ 0 = target then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0)
  calc
    _ = ∑ σ : Equiv.Perm (Fin (n+1)),
        if σ 0 = target then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0 := by
      simpa only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_left] using hslot
    _ = _ := by
      rw [← Equiv.Perm.decomposeFin.symm.sum_comp
        (fun σ : Equiv.Perm (Fin (n+1)) =>
          if σ 0 = target then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0)]
      simp only [Fintype.sum_prod_type, Equiv.Perm.decomposeFin_symm_apply_zero]
      rw [Fintype.sum_eq_single target]
      · simp only [ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_perm,
          Fintype.card_fin,nsmul_eq_mul]
        rw [Nat.factorial_succ]
        push_cast
        have hn : (Nat.factorial n:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        field_simp
      · intro p hp
        simp only [hp,ite_false,Finset.sum_const_zero]

/-- Independent uniform permutations of the actual distinct source lists
give exactly M^(-K) mass to a prescribed copied product. -/
theorem markedSourceCopiedProduct_permutation_mass {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : J → Fin (n+1) → ℕ) (hsource : ∀ j k, source j k ∈ P j)
    (hdist : ∀ j, Function.Injective (source j)) (slot : Fin (n+1)) (a : J → Fin (n+1)) :
    (∑ σ : J → Equiv.Perm (Fin (n+1)),
      if markedSourceCopiedProduct source (fun j => σ j slot) = markedSourceCopiedProduct source a then
        ∏ _j : J, 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0) =
      (n+1:ℝ)⁻¹^(Fintype.card J) := by
  classical
  have heq (σ : J → Equiv.Perm (Fin (n+1))) :
      (if markedSourceCopiedProduct source (fun j => σ j slot) = markedSourceCopiedProduct source a then
        ∏ _j : J, 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0) =
      ∏ j, if σ j slot = a j then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0 := by
    have hi : markedSourceCopiedProduct source (fun j => σ j slot) = markedSourceCopiedProduct source a ↔
        ∀ j, σ j slot = a j := by
      rw [(markedSourceCopiedProduct_injective P hprime hdis source hsource hdist).eq_iff]
      exact funext_iff
    by_cases hall : ∀ j, σ j slot = a j
    · rw [ite_eq_left (hi.mpr hall)]
      apply Finset.prod_congr rfl
      intro j _
      rw [ite_eq_left (hall j)]
    · rw [ite_eq_right (fun he => hall (hi.mp he))]
      obtain ⟨j,hj⟩ := not_forall.mp hall
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [ite_eq_right hj])).symm
  simp_rw [heq]
  calc
    _ = ∏ j, ∑ σ : Equiv.Perm (Fin (n+1)),
        if σ slot = a j then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0 :=
      (Fintype.prod_sum (fun j (σ : Equiv.Perm (Fin (n+1))) =>
        if σ slot = a j then 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0)).symm
    _ = _ := by
      simp_rw [markedPermutation_slot_probability]
      simp only [Finset.prod_const,Finset.card_univ,one_div]

theorem markedSourceCopiedProduct_permutation_mass_le {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : J → Fin (n+1) → ℕ) (hsource : ∀ j k, source j k ∈ P j)
    (hdist : ∀ j, Function.Injective (source j)) (slot : Fin (n+1)) (D : ℕ) :
    (∑ σ : J → Equiv.Perm (Fin (n+1)),
      if markedSourceCopiedProduct source (fun j => σ j slot) = D then
        ∏ _j : J, 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0) ≤
      (n+1:ℝ)⁻¹^(Fintype.card J) := by
  classical
  by_cases hD : ∃ a, markedSourceCopiedProduct source a = D
  · obtain ⟨a,rfl⟩ := hD
    exact (markedSourceCopiedProduct_permutation_mass n P hprime hdis source hsource hdist slot a).le
  · have hz : (∑ σ : J → Equiv.Perm (Fin (n+1)),
        if markedSourceCopiedProduct source (fun j => σ j slot) = D then
          ∏ _j : J, 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      exact ite_eq_right (fun he => hD ⟨_,he⟩)
    rw [hz]
    positivity

theorem markedSourceFull_coprime_promoted_of_cross_ban {J R : Type*}
    [Fintype J] [Fintype R] {M : ℕ} (source : J → Fin M → ℕ)
    (hprime : ∀ j k, (source j k).Prime) (fresh : R → ℕ)
    (hfresh : ∀ r, (fresh r).Prime) (hban : ∀ j k r, source j k ≠ fresh r) :
    (markedSourceFullProduct source).Coprime (∏ r, fresh r) := by
  apply markedSourceFull_coprime_of_ban source hprime
  intro j k hd
  obtain ⟨r,hr⟩ := marked_prime_dvd_tuple_product (hprime j k) fresh hfresh hd
  exact hban j k r hr

theorem markedDirtyOmissionTuple_eq_of_numeric_product_eq {J : Type*} [Fintype J] {M : ℕ}
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : J → Fin M → ℕ) (hsource : ∀ j k, source j k ∈ P j)
    (hdist : ∀ j, Function.Injective (source j)) (a b : J → Fin M) {Z₁ Z₂ : ℕ}
    (hban₁ : ∀ j k, ¬source j k ∣ Z₁) (hban₂ : ∀ j k, ¬source j k ∣ Z₂)
    (he : markedSourceCopiedProduct source a*Z₁ = markedSourceCopiedProduct source b*Z₂) :
    a = b ∧ Z₁ = Z₂ := by
  have hp : 0 < markedSourceFullProduct source :=
    Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (hprime j _ (hsource j k)).pos))
  obtain ⟨hd,hz⟩ := marked_source_ban_product_separation hp
    (markedSourceCopied_dvd_full source a) (markedSourceCopied_dvd_full source b)
    (markedSourceFull_coprime_of_ban source (fun j k => hprime j _ (hsource j k)) hban₁)
    (markedSourceFull_coprime_of_ban source (fun j k => hprime j _ (hsource j k)) hban₂) he
  exact ⟨markedSourceCopiedProduct_injective P hprime hdis source hsource hdist hd,hz⟩

end ArtinMatthews
