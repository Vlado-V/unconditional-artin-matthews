module

public import ArtinMatthews.FixedURootReciprocal


set_option backward.privateInPublic true
@[expose] public section

/-! Literal finite-box transport in the reciprocal coordinate regime. -/
namespace ArtinMatthews

open OAI.Erdos970 ErdosHyperbolaError

/-- Every point of the actual counted box has the strict canonical completion
needed by the reciprocal involution. -/
theorem fixedURootReciprocal_box_canonical {S : ℕ} {u₀ c₀ v₀ d₀ u c v : ℤ}
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hβ : β ≤ 1)
    (hx : (⟨u,(c,v)⟩ : Σ _u : ℤ, ℤ × ℤ) ∈
      fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV) :
    ∃ d : ℤ, 1 < u ∧ 1 < v ∧ 0 < c ∧ c < u ∧ 0 < d ∧ d < v ∧
      u*d-v*c = 1 ∧ Int.ModEq (S : ℤ) d d₀ := by
  have hui : u ∈ realIntervalIntegers A B lcU rcU :=
    (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).1
  have huL := (fixedURootReciprocal_interval_bounds hui).1
  have hu1 : 1 < u := by exact_mod_cast hA.trans_le huL
  have hu : 0 < u := by omega
  obtain ⟨_hui,hci,hvi,_hur,_hcr,_hvr,d,hdet,hdr⟩ :=
    (fixedURootReciprocal_mem_box hu A B α β C D lcU rcU lcC rcC lcV rcV).mp hx
  have hvL := (fixedURootReciprocal_interval_bounds hvi).1
  have hv1 : 1 < v := by exact_mod_cast hC.trans_le hvL
  obtain ⟨hcL,hcR⟩ := fixedURootReciprocal_interval_bounds hci
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hc₀ : 0 ≤ c := by
    exact_mod_cast (mul_nonneg huR.le hα).trans hcL
  have hc₁ : c ≤ u := by
    exact_mod_cast hcR.trans (mul_le_of_le_one_right huR.le hβ)
  obtain ⟨hcpos,hclt,hdpos,hdlt⟩ :=
    fixedURootReciprocal_completion_bounds hu1 hv1 hc₀ hc₁ hdet
  exact ⟨d,hu1,hv1,hcpos,hclt,hdpos,hdlt,hdet,hdr⟩

/-- The literal triple map is an involution at every actually counted point. -/
theorem fixedURootReciprocal_box_involutive {S : ℕ} {u₀ c₀ v₀ d₀ : ℤ}
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hβ : β ≤ 1)
    {x : Σ _u : ℤ, ℤ × ℤ}
    (hx : x ∈ fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D
      lcU rcU lcC rcC lcV rcV) :
    fixedURootReciprocalPoint (fixedURootReciprocalPoint x) = x := by
  rcases x with ⟨u,c,v⟩
  obtain ⟨d,hu,hv,_hc₀,_hc₁,_hd₀,_hd₁,hdet,_hdr⟩ :=
    fixedURootReciprocal_box_canonical hA hC hα hβ hx
  exact fixedURootReciprocalPoint_involutive (by omega) (by omega) hdet

/-- The reciprocal image lies in the reflected root interval enlarged by the
actual uniform displacement `1/(AC)` and clipped to the canonical interval. -/
theorem fixedURootReciprocal_box_outer {S : ℕ} {u₀ c₀ v₀ d₀ : ℤ}
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hβ : β ≤ 1)
    {x : Σ _u : ℤ, ℤ × ℤ}
    (hx : x ∈ fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D
      lcU rcU lcC rcC lcV rcV) :
    fixedURootReciprocalPoint x ∈
      fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
        C D (max 0 (1-β-1/(A*C))) (1-α) A B lcV rcV true true lcU rcU := by
  rcases x with ⟨u,c,v⟩
  obtain ⟨d,hu1,hv1,hcpos,_hclt,_hdpos,hdlt,hdet,hdr⟩ :=
    fixedURootReciprocal_box_canonical hA hC hα hβ hx
  have hu : 0 < u := by omega
  have hv : 0 < v := by omega
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  obtain ⟨hui,hci,hvi,hur,hcr,hvr,_hd⟩ :=
    (fixedURootReciprocal_mem_box hu A B α β C D lcU rcU lcC rcC lcV rcV).mp hx
  have huL := (fixedURootReciprocal_interval_bounds hui).1
  have hvL := (fixedURootReciprocal_interval_bounds hvi).1
  obtain ⟨hcL,hcR⟩ := fixedURootReciprocal_interval_bounds hci
  have hrL : α ≤ (c : ℝ)/(u : ℝ) := (le_div_iff₀ huR).mpr (by simpa [mul_comm] using hcL)
  have hrR : (c : ℝ)/(u : ℝ) ≤ β := (div_le_iff₀ huR).mpr (by simpa [mul_comm] using hcR)
  have heps := fixedURootReciprocal_shift_le (by linarith : 0 < A)
    (by linarith : 0 < C) huL hvL
  have heps₀ : 0 ≤ 1/((u : ℝ)*(v : ℝ)) := by positivity
  have hratio := fixedURootReciprocal_ratio (by omega : u ≠ 0) (by omega : v ≠ 0) hdet
  have hcp : (0 : ℝ) < ((v-d : ℤ) : ℝ) := by exact_mod_cast (sub_pos.mpr hdlt)
  rw [fixedURootReciprocalPoint_completion (by omega : u ≠ 0) hdet]
  apply (fixedURootReciprocal_mem_box hv C D (max 0 (1-β-1/(A*C))) (1-α)
    A B lcV rcV true true lcU rcU).mpr
  refine ⟨hvi,?_,hui,hvr,hvr.sub hdr,hur,u-c,fixedURootReciprocal_det hdet,hur.sub hcr⟩
  apply (fixedURootReciprocal_scaled_interval hvR true true (v-d)).mpr
  simp only [ite_true]
  constructor
  · exact max_le (div_pos hcp hvR).le (by linarith)
  · linarith

/-- An actual injective map gives the finite outer-count inequality. -/
theorem fixedURootReciprocal_card_le_outer {S : ℕ} {u₀ c₀ v₀ d₀ : ℤ}
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hβ : β ≤ 1) :
    (fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV).card ≤
      (fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
        C D (max 0 (1-β-1/(A*C))) (1-α) A B lcV rcV true true lcU rcU).card := by
  apply Finset.card_le_card_of_injOn fixedURootReciprocalPoint
    (fun _x hx => fixedURootReciprocal_box_outer hA hC hα hβ hx)
  intro x hx y hy hxy
  calc
    x = fixedURootReciprocalPoint (fixedURootReciprocalPoint x) :=
      (fixedURootReciprocal_box_involutive hA hC hα hβ hx).symm
    _ = fixedURootReciprocalPoint (fixedURootReciprocalPoint y) := congrArg _ hxy
    _ = y := fixedURootReciprocal_box_involutive hA hC hα hβ hy

/-- A reflected interval shortened by the uniform displacement maps into the
original box. Open root endpoints make this valid for every endpoint convention
of the original box, including a root interval of width at most the displacement. -/
theorem fixedURootReciprocal_box_inner {S : ℕ} {u₀ c₀ v₀ d₀ : ℤ}
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1)
    {x : Σ _u : ℤ, ℤ × ℤ}
    (hx : x ∈ fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
      C D (1-β) (max (1-β) (1-α-1/(A*C))) A B lcV rcV false false lcU rcU) :
    fixedURootReciprocalPoint x ∈
      fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV := by
  rcases x with ⟨u,c,v⟩
  have hδ : 0 ≤ 1/(A*C) := by positivity
  have hγ : 0 ≤ 1-β := by linarith
  have hη : max (1-β) (1-α-1/(A*C)) ≤ 1 := max_le (by linarith) (by linarith)
  obtain ⟨d,hu1,hv1,_hcpos,_hclt,_hdpos,_hdlt,hdet,hdr⟩ :=
    fixedURootReciprocal_box_canonical hC hA hγ hη hx
  have hu : 0 < u := by omega
  have hv : 0 < v := by omega
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  obtain ⟨hui,hci,hvi,hur,hcr,hvr,_hd⟩ :=
    (fixedURootReciprocal_mem_box hu C D (1-β) (max (1-β) (1-α-1/(A*C)))
      A B lcV rcV false false lcU rcU).mp hx
  have huL := (fixedURootReciprocal_interval_bounds hui).1
  have hvL := (fixedURootReciprocal_interval_bounds hvi).1
  have heps : 1/((u : ℝ)*(v : ℝ)) ≤ 1/(A*C) := by
    simpa only [mul_comm C A] using
      fixedURootReciprocal_shift_le (by linarith : 0 < C) (by linarith : 0 < A) huL hvL
  have heps₀ : 0 ≤ 1/((u : ℝ)*(v : ℝ)) := by positivity
  have hroot := (fixedURootReciprocal_scaled_interval huR false false c).mp hci
  change 1-β < (c : ℝ)/(u : ℝ) ∧
    (c : ℝ)/(u : ℝ) < max (1-β) (1-α-1/(A*C)) at hroot
  have hrR : (c : ℝ)/(u : ℝ) < 1-α-1/(A*C) := by
    rcases lt_max_iff.mp hroot.2 with h | h
    · linarith [hroot.1]
    · exact h
  have hratio := fixedURootReciprocal_ratio (by omega : u ≠ 0) (by omega : v ≠ 0) hdet
  have hnewL : α < ((v-d : ℤ) : ℝ)/(v : ℝ) := by linarith
  have hnewR : ((v-d : ℤ) : ℝ)/(v : ℝ) < β := by linarith [hroot.1]
  rw [fixedURootReciprocalPoint_completion (by omega : u ≠ 0) hdet]
  apply (fixedURootReciprocal_mem_box hv A B α β C D lcU rcU lcC rcC lcV rcV).mpr
  refine ⟨hvi,?_,hui,hvr,?_,hur,u-c,fixedURootReciprocal_det hdet,?_⟩
  · apply (fixedURootReciprocal_scaled_interval hvR lcC rcC (v-d)).mpr
    constructor
    · cases lcC
      · exact hnewL
      · exact hnewL.le
    · cases rcC
      · exact hnewR
      · exact hnewR.le
  · simpa only [sub_sub_cancel] using hvr.sub hdr
  · simpa only [sub_sub_cancel] using hur.sub hcr

/-- The finite inner-count inequality comes from the same literal involution. -/
theorem fixedURootReciprocal_inner_le_card {S : ℕ} {u₀ c₀ v₀ d₀ : ℤ}
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    (fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
      C D (1-β) (max (1-β) (1-α-1/(A*C))) A B lcV rcV false false lcU rcU).card ≤
      (fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV).card := by
  have hδ : 0 ≤ 1/(A*C) := by positivity
  have hγ : 0 ≤ 1-β := by linarith
  have hη : max (1-β) (1-α-1/(A*C)) ≤ 1 := max_le (by linarith) (by linarith)
  apply Finset.card_le_card_of_injOn fixedURootReciprocalPoint
    (fun _x hx => fixedURootReciprocal_box_inner hA hC hα hαβ hβ hx)
  intro x hx y hy hxy
  calc
    x = fixedURootReciprocalPoint (fixedURootReciprocalPoint x) :=
      (fixedURootReciprocal_box_involutive hC hA hγ hη hx).symm
    _ = fixedURootReciprocalPoint (fixedURootReciprocalPoint y) := congrArg _ hxy
    _ = y := fixedURootReciprocal_box_involutive hC hA hγ hη hy

/-- The actual reciprocal root count is sandwiched between two root boxes
with the smaller coordinate placed first and with the transformed matrix residue. -/
theorem fixedURootReciprocal_card_sandwich {S : ℕ} {u₀ c₀ v₀ d₀ : ℤ}
    {A B α β C D : ℝ} {lcU rcU lcC rcC lcV rcV : Bool}
    (hA : 1 < A) (hC : 1 < C) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    (fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
      C D (1-β) (max (1-β) (1-α-1/(A*C))) A B lcV rcV false false lcU rcU).card ≤
      (fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV).card ∧
    (fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV).card ≤
      (fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
        C D (max 0 (1-β-1/(A*C))) (1-α) A B lcV rcV true true lcU rcU).card :=
  ⟨fixedURootReciprocal_inner_le_card hA hC hα hαβ hβ,
    fixedURootReciprocal_card_le_outer hA hC hα hβ⟩

end ArtinMatthews
