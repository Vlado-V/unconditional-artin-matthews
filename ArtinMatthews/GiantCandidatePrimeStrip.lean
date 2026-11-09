module

public import ArtinMatthews.ShiftedCommonPrimePart
public import ArtinMatthews.GiantOrdinaryProxyTuple


set_option backward.privateInPublic true
@[expose] public section

/-! Full candidate prime powers are removed from the threshold and
logarithm in the ordinary proxy. Roughness is still tested at the
original integer. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

abbrev giantCandidatePrimePart (P : Finset ℕ) (m : ℕ) : ℕ :=
  commonPrimePart m (∏ p ∈ P,p)

def giantCandidateStrip (P : Finset ℕ) (m : ℕ) : ℕ :=
  m / giantCandidatePrimePart P m

def giantCandidateRemovedLog (P : Finset ℕ) (m : ℕ) : ℝ :=
  Real.log (giantCandidatePrimePart P m:ℝ)

theorem giantCandidatePrimePart_mul_strip (P : Finset ℕ) (m : ℕ) :
    giantCandidatePrimePart P m * giantCandidateStrip P m = m :=
  Nat.mul_div_cancel' (commonPrimePart_dvd _ _)

theorem giantCandidateStrip_pos (P : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    0 < giantCandidateStrip P m :=
  Nat.div_pos (Nat.le_of_dvd hm (commonPrimePart_dvd _ _))
    (Nat.pos_of_ne_zero (commonPrimePart_ne_zero hm.ne' _))

theorem giantCandidateStrip_le (P : Finset ℕ) (m : ℕ) :
    giantCandidateStrip P m ≤ m := Nat.div_le_self _ _

theorem giantCandidateStrip_coprime (P : Finset ℕ) {m : ℕ} (hm : m ≠ 0) :
    (∏ p ∈ P,p).Coprime (giantCandidateStrip P m) :=
  coprime_commonPrimePart_quotient hm _

theorem giantCandidateRemovedLog_eq_sub (P : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    giantCandidateRemovedLog P m = Real.log (m:ℝ)-Real.log (giantCandidateStrip P m:ℝ) := by
  have hp : (giantCandidatePrimePart P m:ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (commonPrimePart_ne_zero hm.ne' _)
  have hs : (giantCandidateStrip P m:ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (giantCandidateStrip_pos P hm).ne'
  have he : (giantCandidatePrimePart P m:ℝ)*(giantCandidateStrip P m:ℝ) = (m:ℝ) := by
    exact_mod_cast giantCandidatePrimePart_mul_strip P m
  have hh := Real.log_mul hp hs
  rw [he] at hh
  unfold giantCandidateRemovedLog
  linarith only [hh]

theorem giantCandidateRemovedLog_nonneg (P : Finset ℕ) (m : ℕ) :
    0 ≤ giantCandidateRemovedLog P m := Real.log_natCast_nonneg _

theorem giantCandidateRemovedLog_le (P : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    giantCandidateRemovedLog P m ≤ Real.log (m:ℝ) := by
  rw [giantCandidateRemovedLog_eq_sub P hm]
  exact sub_le_self _ (Real.log_natCast_nonneg _)

theorem giantCandidateStrip_mul_prime (P : Finset ℕ) {p m : ℕ}
    (hp : p.Prime) (hpP : p ∈ P) (hm : 0 < m) :
    giantCandidateStrip P (p*m) = giantCandidateStrip P m := by
  let d := ∏ q ∈ P,q
  have hpd : p ∣ d := dvd_prod_of_mem (fun q : ℕ => q) hpP
  have he : commonPrimePart p d = p := Nat.dvd_antisymm (commonPrimePart_dvd _ _)
    ((prime_dvd_commonPrimePart_iff hp.ne_zero hp d).mpr ⟨dvd_rfl,hpd⟩)
  have hmul : giantCandidatePrimePart P (p*m) = p * giantCandidatePrimePart P m := by
    change commonPrimePart (p*m) d = p*commonPrimePart m d
    rw [commonPrimePart_mul hp.ne_zero hm.ne' d,he]
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos
    (Nat.pos_of_ne_zero (commonPrimePart_ne_zero hm.ne' d)))
  calc
    _ = p*m := by rw [← hmul,giantCandidatePrimePart_mul_strip]
    _ = _ := by rw [mul_assoc,giantCandidatePrimePart_mul_strip]

def giantCandidateStrippedSlotCoefficient (P : Finset ℕ) (W z : ℝ) (m : ℕ) : ℂ :=
  if z < (giantCandidateStrip P m:ℝ) then
    (markedSieveEulerProduct W:ℂ)⁻¹*((Real.log (giantCandidateStrip P m:ℝ))⁻¹:ℝ)*
      (if ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m then 1 else 0)
  else 0

theorem giant_candidate_rough_mul_prime_iff {W : ℝ} (hW : 0 ≤ W)
    {p m : ℕ} (hp : p.Prime) (hpW : W < (p:ℝ)) :
    (∀ r ∈ Nat.primesLE ⌊W⌋₊, ¬r ∣ p*m) ↔
      ∀ r ∈ Nat.primesLE ⌊W⌋₊, ¬r ∣ m := by
  constructor
  · intro h r hr hd
    exact h r hr (dvd_mul_of_dvd_right hd p)
  · intro h r hr hd
    obtain ⟨hr₁,hrP⟩ := Nat.mem_primesLE.mp hr
    have hrW : (r:ℝ) ≤ W := (Nat.cast_le.mpr hr₁).trans (Nat.floor_le hW)
    rcases hrP.dvd_mul.mp hd with hrp | hrm
    · have he : r=p := (Nat.dvd_prime hp).mp hrp |>.resolve_left hrP.ne_one
      exact (not_lt_of_ge hrW) (he.symm ▸ hpW)
    · exact h r hr hrm

theorem giantCandidateStrippedSlotCoefficient_mul_prime (P : Finset ℕ) {W z : ℝ}
    (hW : 0 ≤ W) {p m : ℕ} (hp : p.Prime) (hpP : p ∈ P) (hpW : W < (p:ℝ)) (hm : 0 < m) :
    giantCandidateStrippedSlotCoefficient P W z (p*m) =
      giantCandidateStrippedSlotCoefficient P W z m := by
  unfold giantCandidateStrippedSlotCoefficient
  rw [giantCandidateStrip_mul_prime P hp hpP hm]
  have he : (if ∀ r ∈ Nat.primesLE ⌊W⌋₊, ¬r ∣ p*m then (1:ℂ) else 0) =
      (if ∀ r ∈ Nat.primesLE ⌊W⌋₊, ¬r ∣ m then (1:ℂ) else 0) :=
    ite_cond_congr (propext (giant_candidate_rough_mul_prime_iff hW hp hpW))
  rw [he]

def giantOrdinaryStrippedProxyTupleSum {J : Type*} [Fintype J]
    (P : ℝ → Finset ℕ) (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  (∑ t ∈ giantOrderedProductTuples j ⌊T*x⌋₊, markedExtractionWeight e G Φ x (∏ i,t i) *
    ∏ i,χ (t i)*giantCandidateStrippedSlotCoefficient (P x)
      (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) (t i)) / j.factorial

theorem giantOrdinaryStrippedProxyTupleSum_character_product {J : Type*} [Fintype J]
    (P : ℝ → Finset ℕ) (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ : ℝ) (j : ℕ) (x : ℝ) :
    giantOrdinaryStrippedProxyTupleSum P e χ G Φ T γ j x =
      (∑ t ∈ giantOrderedProductTuples j ⌊T*x⌋₊, markedExtractionWeight e G Φ x (∏ i,t i) *
        χ ((∏ i,t i):ℕ) * ∏ i,giantCandidateStrippedSlotCoefficient (P x)
          (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) (t i)) / j.factorial := by
  unfold giantOrdinaryStrippedProxyTupleSum
  apply congrArg (fun z : ℂ => z/j.factorial)
  apply sum_congr rfl
  intro t _
  simp only [Nat.cast_prod,map_prod,prod_mul_distrib,mul_assoc]

end
end ArtinMatthews
