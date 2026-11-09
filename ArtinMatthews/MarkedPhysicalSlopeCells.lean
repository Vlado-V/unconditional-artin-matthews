module

public import ArtinMatthews.MarkedPhysicalSlopeSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Actual half-open slope cells and a counting bound proved from
integer determinant separation. No cell-cardinality premise is used. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section

theorem markedSeparatedInterval_card {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (a L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ x ∈ s, a ≤ f x ∧ f x ≤ a+L)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ |f x-f y|) :
    (s.card : ℝ) ≤ L+1 := by
  let g : ι → ℤ := fun x => ⌊f x-a⌋
  have hinj : Set.InjOn g s := by
    intro x hx y hy he
    by_contra hne
    have h := hsep x hx y hy hne
    have hxlo := Int.floor_le (f x-a)
    have hxhi := Int.lt_floor_add_one (f x-a)
    have hylo := Int.floor_le (f y-a)
    have hyhi := Int.lt_floor_add_one (f y-a)
    change ⌊f x-a⌋ = ⌊f y-a⌋ at he
    rw [he] at hxlo hxhi
    have hh : |f x-f y| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
    linarith
  have hsub : s.image g ⊆ Finset.Icc (0 : ℤ) ⌊L⌋ := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hlo,hhi⟩ := hf x hx
    exact Finset.mem_Icc.mpr ⟨Int.floor_nonneg.mpr (by linarith),
      Int.floor_mono (by linarith)⟩
  have hc : s.card ≤ (Finset.Icc (0 : ℤ) ⌊L⌋).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hfloor : (0 : ℤ) ≤ ⌊L⌋ := Int.floor_nonneg.mpr hL
  have hi : ((Finset.Icc (0 : ℤ) ⌊L⌋).card : ℤ) = ⌊L⌋+1 := by
    simpa only [sub_zero] using Int.card_Icc_of_le 0 ⌊L⌋ (by omega : (0 : ℤ) ≤ ⌊L⌋+1)
  calc
    _ ≤ ((Finset.Icc (0 : ℤ) ⌊L⌋).card : ℝ) := by exact_mod_cast hc
    _ = (⌊L⌋ : ℝ)+1 := by exact_mod_cast hi
    _ ≤ L+1 := by linarith [Int.floor_le L]

def markedPhysicalSlopeCell (w : ℝ) (p : ℤ × ℤ) : ℤ := ⌊markedPhysicalSlope p/w⌋

theorem markedPhysicalSlopeCell_bounds {w : ℝ} (hw : 0 < w) (p : ℤ × ℤ) (j : ℤ)
    (hj : markedPhysicalSlopeCell w p=j) :
    (j : ℝ)*w ≤ markedPhysicalSlope p ∧ markedPhysicalSlope p < (j : ℝ)*w+w := by
  have hlo := Int.floor_le (markedPhysicalSlope p/w)
  have hhi := Int.lt_floor_add_one (markedPhysicalSlope p/w)
  change ⌊markedPhysicalSlope p/w⌋ = j at hj
  rw [hj] at hlo hhi
  constructor
  · exact (le_div_iff₀ hw).mp hlo
  · have h := (div_lt_iff₀ hw).mp hhi
    nlinarith

theorem markedPhysicalSlopeCell_card (Z : Finset (ℤ × ℤ))
    (hprim : ∀ p ∈ Z, IsCoprime p.1 p.2) (A w : ℝ) (hA : 0 < A) (hw : 0 < w)
    (hfirst : ∀ p ∈ Z, 0 < p.1 ∧ (p.1 : ℝ) ≤ A) (j : ℤ) :
    ((Z.filter (fun p => markedPhysicalSlopeCell w p=j)).card : ℝ) ≤ A^2*w+1 := by
  let s := Z.filter (fun p => markedPhysicalSlopeCell w p=j)
  apply markedSeparatedInterval_card s (fun p => A^2*markedPhysicalSlope p)
    (A^2*((j : ℝ)*w)) (A^2*w) (mul_nonneg (sq_nonneg A) hw.le)
  · intro p hp
    obtain ⟨_,hc⟩ := Finset.mem_filter.mp hp
    have h := markedPhysicalSlopeCell_bounds hw p j hc
    constructor <;> nlinarith [sq_nonneg A]
  · intro p hp q hq hpq
    have hpZ := (Finset.mem_filter.mp hp).1
    have hqZ := (Finset.mem_filter.mp hq).1
    have hs := markedPrimitiveSlope_separated q p (hprim q hqZ) (hprim p hpZ)
      (hfirst q hqZ).1 (hfirst p hpZ).1 hpq.symm A hA (hfirst q hqZ).2 (hfirst p hpZ).2
    have hsq : 0 < A^2 := sq_pos_of_pos hA
    have hmul := (div_le_iff₀ hsq).mp hs
    rw [← mul_sub,abs_mul,abs_of_pos hsq]
    nlinarith

theorem markedPhysicalSlopeCell_box_card (Z : Finset (ℤ × ℤ))
    (hprim : ∀ p ∈ Z, IsCoprime p.1 p.2) (U H B : ℝ)
    (hU : 0 < U) (hH : 0 < H) (hB : 0 < B)
    (hfirst : ∀ p ∈ Z, U ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ B*U) (j : ℤ) :
    ((Z.filter (fun p => markedPhysicalSlopeCell (H/U^2) p=j)).card : ℝ) ≤ B^2*H+1 := by
  have h := markedPhysicalSlopeCell_card Z hprim (B*U) (H/U^2)
    (mul_pos hB hU) (div_pos hH (sq_pos_of_pos hU)) (fun p hp =>
      ⟨by exact_mod_cast hU.trans_le (hfirst p hp).1,(hfirst p hp).2⟩) j
  have he : (B*U)^2*(H/U^2) = B^2*H := by field_simp
  rwa [he] at h

theorem markedPhysicalSlopeCell_sixteen_card (Z : Finset (ℤ × ℤ))
    (hprim : ∀ p ∈ Z, IsCoprime p.1 p.2) (U H : ℝ) (hU : 0 < U) (hH : 0 < H)
    (hfirst : ∀ p ∈ Z, U ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 16*U) (j : ℤ) :
    ((Z.filter (fun p => markedPhysicalSlopeCell (H/U^2) p=j)).card : ℝ) ≤ 256*H+1 := by
  convert markedPhysicalSlopeCell_box_card Z hprim U H 16 hU hH (by norm_num) hfirst j using 1
  norm_num

end
end ArtinMatthews
