module

public import ArtinMatthews.MarkedMinorArcLatticeBox
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Literal homogeneous-congruence counts for the dirty comparison branch.
The interval count reuses the exact ceiling proof from
OAI/NumberTheory/Ostmann/ZeroDensity/ProgressionLiftCount.lean; no distribution
estimate is assumed. Both coordinate directions and arbitrary origins remain. -/
namespace ArtinMatthews
open Finset
noncomputable section

-- Use the canonical additive structure of ZMod throughout field arithmetic.

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
 theorem markedDirtyMajor_integer_residue_count (lo : ℤ) (M p : ℕ) (hp : 0 < p) (r : ZMod p) :
    (((Ico lo (lo+(M:ℤ))).filter (fun n : ℤ => (n:ZMod p)=r)).card:ℝ) ≤ (M:ℝ)/p+1 := by
  let : NeZero p := ⟨hp.ne'⟩
  have heq (n : ℤ) : (n:ZMod p)=r ↔ Int.ModEq (p:ℤ) n (r.val:ℤ) := by
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using
      (ZMod.intCast_eq_intCast_iff n (r.val:ℤ) p)
  simp only [heq]
  let A : ℚ := ((lo:ℚ)-r.val)/p
  let B : ℚ := ((lo+(M:ℤ):ℤ):ℚ)/p-(r.val:ℚ)/p
  have hq : (0:ℤ) < p := by exact_mod_cast hp
  have hcard := Int.Ico_filter_modEq_card lo (lo+(M:ℤ)) hq (r.val:ℤ)
  have hcast : (((Ico lo (lo+(M:ℤ))).filter (fun n => Int.ModEq (p:ℤ) n (r.val:ℤ))).card:ℚ)=
      max (((⌈B⌉:ℤ):ℚ)-((⌈A⌉:ℤ):ℚ)) 0 := by
    dsimp [A,B]
    rw [← sub_div]
    exact_mod_cast hcard
  have hA : A ≤ (⌈A⌉:ℤ) := Int.le_ceil A
  have hB : ((⌈B⌉:ℤ):ℚ) < B+1 := Int.ceil_lt_add_one B
  have hdiff : ((⌈B⌉:ℤ):ℚ)-((⌈A⌉:ℤ):ℚ) ≤ (M:ℚ)/p+1 := by
    have hid : B-A=(M:ℚ)/p := by dsimp [A,B]; push_cast; ring
    linarith
  have hrat : (((Ico lo (lo+(M:ℤ))).filter (fun n => Int.ModEq (p:ℤ) n (r.val:ℤ))).card:ℚ) ≤
      (M:ℚ)/p+1 := by
    rw [hcast]
    exact max_le hdiff (by positivity)
  have hr := Rat.cast_le (K := ℝ) |>.mpr hrat
  simpa only [Rat.cast_natCast,Rat.cast_add,Rat.cast_div,Rat.cast_one] using hr

 def markedDirtyMajorLineBox (p : ℕ) (A B : ZMod p) (lo hi : ℤ) (M N : ℕ) : Finset (ℤ × ℤ) :=
  (markedMinorBox lo hi M N).filter (fun z => A*(z.1:ZMod p)+B*(z.2:ZMod p)=0)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
 theorem markedDirtyMajorLineBox_first {p : ℕ} [Fact p.Prime] (A B : ZMod p) (hA : A ≠ 0)
    (lo hi : ℤ) (M N : ℕ) :
    (markedDirtyMajorLineBox p A B lo hi M N).card ≤
      ∑ v ∈ Ico hi (hi+(N:ℤ)), ((Ico lo (lo+(M:ℤ))).filter
        (fun u : ℤ => (u:ZMod p)=-(B*(v:ZMod p))/A)).card := by
  have heq (u v : ℤ) : A*(u:ZMod p)+B*(v:ZMod p)=0 ↔ (u:ZMod p)=-(B*(v:ZMod p))/A := by
    constructor
    · intro h
      apply (eq_div_iff hA).mpr
      simpa only [mul_comm] using (eq_neg_of_add_eq_zero_left h)
    · intro h
      have hh := (eq_div_iff hA).mp h
      exact (add_eq_zero_iff_eq_neg).mpr (by simpa only [mul_comm] using hh)
  simp only [markedDirtyMajorLineBox,markedMinorBox,product_eq_sprod,card_eq_sum_ones,sum_filter,heq]
  rw [sum_product,sum_comm]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
 theorem markedDirtyMajorLineBox_first_bound {p : ℕ} [Fact p.Prime] (A B : ZMod p) (hA : A ≠ 0)
    (lo hi : ℤ) (M N : ℕ) :
    ((markedDirtyMajorLineBox p A B lo hi M N).card:ℝ) ≤ (M:ℝ)*N/p+N := by
  have hc := markedDirtyMajorLineBox_first A B hA lo hi M N
  have hr : ((markedDirtyMajorLineBox p A B lo hi M N).card:ℝ) ≤
      ∑ v ∈ Ico hi (hi+(N:ℤ)), (((Ico lo (lo+(M:ℤ))).filter
        (fun u : ℤ => (u:ZMod p)=-(B*(v:ZMod p))/A)).card:ℝ) := by exact_mod_cast hc
  apply hr.trans
  calc
    _ ≤ ∑ _v ∈ Ico hi (hi+(N:ℤ)), ((M:ℝ)/p+1) :=
      sum_le_sum (fun v _ => markedDirtyMajor_integer_residue_count lo M p (Fact.out : p.Prime).pos _)
    _ = _ := by
      simp only [sum_const,nsmul_eq_mul,Int.card_Ico,add_sub_cancel_left,Int.toNat_natCast]
      ring

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
 theorem markedDirtyMajorLineBox_swap (p : ℕ) (A B : ZMod p) (lo hi : ℤ) (M N : ℕ) :
    (markedDirtyMajorLineBox p A B lo hi M N).card=(markedDirtyMajorLineBox p B A hi lo N M).card := by
  classical
  apply card_nbij' Prod.swap Prod.swap
  · intro z hz
    change z ∈ markedDirtyMajorLineBox p A B lo hi M N at hz
    change z.swap ∈ markedDirtyMajorLineBox p B A hi lo N M
    simp only [markedDirtyMajorLineBox,mem_filter,markedMinorBox,product_eq_sprod,mem_product,Prod.fst_swap,Prod.snd_swap] at hz ⊢
    exact ⟨⟨hz.1.2,hz.1.1⟩,by simpa only [add_comm] using hz.2⟩
  · intro z hz
    change z ∈ markedDirtyMajorLineBox p B A hi lo N M at hz
    change z.swap ∈ markedDirtyMajorLineBox p A B lo hi M N
    simp only [markedDirtyMajorLineBox,mem_filter,markedMinorBox,product_eq_sprod,mem_product,Prod.fst_swap,Prod.snd_swap] at hz ⊢
    exact ⟨⟨hz.1.2,hz.1.1⟩,by simpa only [add_comm] using hz.2⟩
  · intro z _
    exact Prod.swap_swap z
  · intro z _
    exact Prod.swap_swap z

 /- The actual nonzero homogeneous line has the precise area/p plus one
long-side error; primitive-vector restrictions may be discarded safely. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
 theorem markedDirtyMajorLineBox_count {p : ℕ} (hp : p.Prime) (A B : ZMod p)
    (hAB : A ≠ 0 ∨ B ≠ 0) (lo hi : ℤ) (M N : ℕ) :
    ((markedDirtyMajorLineBox p A B lo hi M N).card:ℝ) ≤ (M:ℝ)*N/p+max (M:ℝ) N := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hAB with hA|hB
  · exact (markedDirtyMajorLineBox_first_bound A B hA lo hi M N).trans
      (add_le_add le_rfl (le_max_right _ _))
  · rw [markedDirtyMajorLineBox_swap]
    have hb := markedDirtyMajorLineBox_first_bound B A hB hi lo N M
    calc
      _ ≤ (N:ℝ)*M/p+M := hb
      _ ≤ (N:ℝ)*M/p+max (M:ℝ) N := add_le_add le_rfl (le_max_left _ _)
      _ = _ := by ring

end
end ArtinMatthews
