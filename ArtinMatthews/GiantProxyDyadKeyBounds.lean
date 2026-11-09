module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The full finite family of dyadic boxes of an ordered product.
Retaining the total exponent and erasing one coordinate gives the
weighted count, including a restriction on one other coordinate. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

def giantProxyDyadKeys (j N : ℕ) : Finset (Fin j → ℕ) :=
  (Fintype.piFinset (fun _ : Fin j => range (Nat.log 2 N + 1))).filter
    (fun key => (∑ i, key i) ≤ Nat.log 2 N)

def giantProxyDyadKeyWeight {j : ℕ} (key : Fin j → ℕ) : ℝ :=
  ((2 ^ (∑ i, key i) : ℕ) : ℝ)

theorem mem_giantProxyDyadKeys {j N : ℕ} {key : Fin j → ℕ} :
    key ∈ giantProxyDyadKeys j N ↔
      (∀ i, key i < Nat.log 2 N + 1) ∧ (∑ i, key i) ≤ Nat.log 2 N := by
  simp only [giantProxyDyadKeys, mem_filter, Fintype.mem_piFinset, mem_range]

/-- The actual lower dyadic heights multiply to the key weight. -/
theorem giantProxyDyadKeyWeight_eq_prod {j : ℕ} (key : Fin j → ℕ) :
    giantProxyDyadKeyWeight key = ∏ i, (2 : ℝ) ^ key i := by
  rw [giantProxyDyadKeyWeight, Nat.cast_pow, Nat.cast_ofNat, prod_pow_eq_pow_sum]

def giantProxyDyadKey {j : ℕ} (t : Fin j → ℕ) : Fin j → ℕ :=
  fun i => Nat.log 2 (t i)

theorem giantProxyDyadKey_lower_upper {j : ℕ} (t : Fin j → ℕ) (i : Fin j)
    (ht : 0 < t i) :
    (2 : ℕ) ^ giantProxyDyadKey t i ≤ t i ∧
      t i < (2 : ℕ) ^ (giantProxyDyadKey t i + 1) :=
  ⟨Nat.pow_log_le_self 2 ht.ne', Nat.lt_pow_succ_log_self (by decide) _⟩

/-- The actual key of a positive tuple lies in the finite family at its
original product cutoff. -/
theorem giantProxyDyadKey_mem {j N : ℕ} (t : Fin j → ℕ)
    (ht : ∀ i, 0 < t i) (hN : (∏ i, t i) ≤ N) :
    giantProxyDyadKey t ∈ giantProxyDyadKeys j N := by
  have hN0 : 0 < N := (prod_pos (fun i _ => ht i)).trans_le hN
  have hpow : (2 : ℕ) ^ (∑ i, giantProxyDyadKey t i) ≤ N := by
    rw [← prod_pow_eq_pow_sum]
    exact (prod_le_prod (fun i _ => (giantProxyDyadKey_lower_upper t i (ht i)).1)).trans hN
  have hs := (Nat.le_log_iff_pow_le (by decide : 1 < 2) hN0.ne').mpr hpow
  refine mem_giantProxyDyadKeys.mpr ⟨?_, hs⟩
  intro i
  exact Nat.lt_succ_of_le ((single_le_sum (fun k _ => Nat.zero_le (giantProxyDyadKey t k))
    (mem_univ i)).trans hs)

private theorem dyadKeySum_le_erase_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Finset ℕ) (pivot : ι) (K : ℕ) :
    (∑ key ∈ (Fintype.piFinset A).filter (fun key => (∑ i, key i) ≤ K),
      (2 : ℝ) ^ (∑ i, key i)) ≤
      ((∏ i ∈ (univ : Finset ι).erase pivot, (A i).card : ℕ) : ℝ) *
        ∑ s ∈ range (K + 1), (2 : ℝ) ^ s := by
  classical
  let E := (univ : Finset ι).erase pivot
  let T := Fintype.piFinset (fun i : E => A i.val)
  let S := (Fintype.piFinset A).filter (fun key => (∑ i, key i) ≤ K)
  let encode (key : ι → ℕ) : (E → ℕ) × ℕ := (fun i => key i.val, ∑ i, key i)
  have hencode : Function.Injective encode := by
    intro key other he
    have hrest (i : E) : key i.val = other i.val := congrFun (congrArg Prod.fst he) i
    have htotal : (∑ i, key i) = ∑ i, other i := congrArg Prod.snd he
    have hsub : (∑ i ∈ E, key i) = ∑ i ∈ E, other i :=
      sum_congr rfl (fun i hi => hrest ⟨i, hi⟩)
    have hk := sum_erase_add (univ : Finset ι) key (mem_univ pivot)
    have ho := sum_erase_add (univ : Finset ι) other (mem_univ pivot)
    change (∑ i ∈ E, key i) + key pivot = ∑ i, key i at hk
    change (∑ i ∈ E, other i) + other pivot = ∑ i, other i at ho
    have hp : key pivot = other pivot := by omega
    funext i
    by_cases hi : i = pivot
    · exact hi ▸ hp
    · exact hrest ⟨i, mem_erase.mpr ⟨hi, mem_univ i⟩⟩
  have hmem (key : ι → ℕ) (hk : key ∈ S) : encode key ∈ T ×ˢ range (K + 1) := by
    obtain ⟨hval, htotal⟩ := mem_filter.mp hk
    exact mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mp hval i.val),
      mem_range.mpr (Nat.lt_succ_of_le htotal)⟩
  calc
    _ ≤ ∑ x ∈ T ×ˢ range (K + 1), (2 : ℝ) ^ x.2 :=
      sum_le_sum_of_injOn encode hencode.injOn (by
        intro x hx
        obtain ⟨key, hk, rfl⟩ := mem_image.mp hx
        exact hmem key hk)
        (fun _ _ => le_rfl) (fun _ _ _ => by positivity)
    _ = (T.card : ℝ) * ∑ s ∈ range (K + 1), (2 : ℝ) ^ s := by
      rw [sum_product]
      change (∑ _x ∈ T, ∑ y ∈ range (K + 1), (2 : ℝ) ^ y) = _
      rw [sum_const, nsmul_eq_mul]
    _ = _ := by
      have hc : T.card = ∏ i ∈ E, (A i).card := by
        unfold T
        rw [Fintype.card_piFinset]
        exact prod_coe_sort E (fun i => (A i).card)
      rw [hc]

private theorem dyadKey_geom_sum_le (N : ℕ) (hN : 0 < N) :
    (∑ s ∈ range (Nat.log 2 N + 1), (2 : ℝ) ^ s) ≤ 2 * (N : ℝ) := by
  have hsum (k : ℕ) : (∑ s ∈ range k, (2 : ℝ) ^ s) + 1 = 2 ^ k := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [sum_range_succ, pow_succ, ← hk]
      ring
  have hp : (2 : ℝ) ^ Nat.log 2 N ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
  calc
    _ ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) := by linarith [hsum (Nat.log 2 N + 1)]
    _ ≤ _ := by rw [pow_succ, mul_comm (2 : ℝ)]; exact mul_le_mul_of_nonneg_right hp (by norm_num)

theorem giantProxyDyadKeys_weight_sum_le (j N : ℕ) (hj : 1 ≤ j) (hN : 0 < N) :
    (∑ key ∈ giantProxyDyadKeys j N, giantProxyDyadKeyWeight key) ≤
      2 * (N : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ (j - 1) := by
  let pivot : Fin j := ⟨0, by omega⟩
  let K := Nat.log 2 N
  have h := dyadKeySum_le_erase_product (fun _ : Fin j => range (K + 1)) pivot K
  simp only [card_range, prod_const, card_erase_of_mem (mem_univ pivot),
    card_univ, Fintype.card_fin, Nat.cast_pow] at h
  unfold giantProxyDyadKeys giantProxyDyadKeyWeight
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ ≤ ((K + 1 : ℕ) : ℝ) ^ (j - 1) * ∑ s ∈ range (K + 1), (2 : ℝ) ^ s := h
    _ ≤ ((K + 1 : ℕ) : ℝ) ^ (j - 1) * (2 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (dyadKey_geom_sum_le N hN) (by positivity)
    _ = _ := mul_comm _ _

theorem giantProxyDyadKeys_restricted_weight_sum_le (j N : ℕ) (hj : 2 ≤ j)
    (hN : 0 < N) (i : Fin j) (I : Finset ℕ) :
    (∑ key ∈ (giantProxyDyadKeys j N).filter (fun key => key i ∈ I), giantProxyDyadKeyWeight key) ≤
      2 * (N : ℝ) * (I.card : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ (j - 2) := by
  classical
  let K := Nat.log 2 N
  obtain ⟨pivot, hp⟩ : ∃ p : Fin j, p ≠ i := by
    let zero : Fin j := ⟨0, by omega⟩
    let one : Fin j := ⟨1, by omega⟩
    by_cases hi : zero = i
    · refine ⟨one, fun h => ?_⟩
      have hz : (1 : ℕ) = 0 := congrArg Fin.val (h.trans hi.symm)
      omega
    · exact ⟨zero, hi⟩
  let E := (univ : Finset (Fin j)).erase pivot
  let A (v : Fin j) : Finset ℕ :=
    if v = i then I ∩ range (K + 1) else range (K + 1)
  have hAi : A i = I ∩ range (K + 1) := ite_eq_left rfl
  have hAv (v : Fin j) (hv : v ≠ i) : A v = range (K + 1) := ite_eq_right hv
  have hkeys : (giantProxyDyadKeys j N).filter (fun key => key i ∈ I) =
      (Fintype.piFinset A).filter (fun key => (∑ v, key v) ≤ K) := by
    ext key
    simp only [mem_filter, mem_giantProxyDyadKeys, Fintype.mem_piFinset]
    constructor
    · rintro ⟨⟨hcoord, htotal⟩, hi⟩
      refine ⟨?_, htotal⟩
      intro v
      by_cases hv : v = i
      · subst v
        rw [hAi]
        exact mem_inter.mpr ⟨hi, mem_range.mpr (hcoord i)⟩
      · rw [hAv v hv]
        exact mem_range.mpr (hcoord v)
    · rintro ⟨hcoord, htotal⟩
      have hi : key i ∈ I ∩ range (K + 1) := by simpa only [A, ite_true] using hcoord i
      refine ⟨⟨?_, htotal⟩, (mem_inter.mp hi).1⟩
      intro v
      by_cases hv : v = i
      · subst v
        exact mem_range.mp (mem_inter.mp hi).2
      · exact mem_range.mp (by simpa only [A, ite_eq_right hv] using hcoord v)
  have hiE : i ∈ E := mem_erase.mpr ⟨Ne.symm hp, mem_univ i⟩
  have hcount : (∏ v ∈ E, (A v).card) ≤ I.card * (K + 1) ^ (j - 2) := by
    have hrest : (∏ v ∈ E.erase i, (A v).card) = (K + 1) ^ (j - 2) := by
      calc
        _ = ∏ _v ∈ E.erase i, (K + 1) := by
          apply prod_congr rfl
          intro v hv
          simp only [A, ite_eq_right (mem_erase.mp hv).1, card_range]
        _ = _ := by
          rw [prod_const, card_erase_of_mem hiE]
          simp only [E, card_erase_of_mem (mem_univ pivot), card_univ, Fintype.card_fin]
          congr 1
    rw [← prod_erase_mul E (fun v => (A v).card) hiE, hrest]
    rw [mul_comm I.card, hAi]
    exact Nat.mul_le_mul_left _ (card_le_card (inter_subset_left : I ∩ range (K + 1) ⊆ I))
  have h := dyadKeySum_le_erase_product A pivot K
  have hcountR : ((∏ v ∈ E, (A v).card : ℕ) : ℝ) ≤
      (I.card : ℝ) * ((K + 1 : ℕ) : ℝ) ^ (j - 2) := by exact_mod_cast hcount
  have hsum0 : 0 ≤ ∑ s ∈ range (K + 1), (2 : ℝ) ^ s :=
    sum_nonneg (fun s _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s)
  have hcount0 : 0 ≤ (I.card : ℝ) * ((K + 1 : ℕ) : ℝ) ^ (j - 2) :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  rw [hkeys]
  unfold giantProxyDyadKeyWeight
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ ≤ ((∏ v ∈ E, (A v).card : ℕ) : ℝ) * ∑ s ∈ range (K + 1), (2 : ℝ) ^ s := h
    _ ≤ ((I.card : ℝ) * ((K + 1 : ℕ) : ℝ) ^ (j - 2)) * (2 * (N : ℝ)) :=
      mul_le_mul hcountR (dyadKey_geom_sum_le N hN) hsum0 hcount0
    _ = _ := by dsimp only [K]; ring

end
end ArtinMatthews
