module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring


set_option backward.privateInPublic true
@[expose] public section

/-! A finite set of separated slopes on a bounded interval.
Assigning each slope to an integer interval gives the linear packing bound. -/

noncomputable section
open Set

namespace ArtinMatthews

theorem spectral_card_le_separated_slopes {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hf : ∀ i ∈ s, |f i| ≤ 1)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |f i-f j|) :
    (s.card : ℝ) ≤ 1+2/δ := by
  let z (i : ι) := (f i+1)/δ
  let I := Finset.Icc (0 : ℤ) ⌊(2 : ℝ)/δ⌋
  let g (i : ι) : ℤ := ⌊z i⌋
  have hmaps : Set.MapsTo g (s : Set ι) (I : Set ℤ) := by
    intro i hi
    obtain ⟨hlo,hhi⟩ := abs_le.mp (hf i hi)
    apply Finset.mem_Icc.mpr
    refine ⟨Int.floor_nonneg.mpr (div_nonneg (by linarith) hδ.le),
      Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hδ.le)⟩
  have hinj : (s : Set ι).InjOn g := by
    intro i hi j hj he
    by_contra hne
    have hil := Int.floor_le (z i)
    have hiu := Int.lt_floor_add_one (z i)
    have hjl := Int.floor_le (z j)
    have hju := Int.lt_floor_add_one (z j)
    change ⌊z i⌋ = ⌊z j⌋ at he
    rw [he] at hil hiu
    have hd : |z i-z j| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
    have hsub : z i-z j = (f i-f j)/δ := by dsimp only [z]; ring
    rw [hsub,abs_div,abs_of_pos hδ] at hd
    have hd' := (div_lt_iff₀ hδ).mp hd
    linarith [hgap i hi j hj hne]
  have hc := Finset.card_le_card_of_injOn g hmaps hinj
  have hfloor : 0 ≤ ⌊(2 : ℝ)/δ⌋ := Int.floor_nonneg.mpr (by positivity)
  have hInt : (I.card : ℤ) = ⌊(2 : ℝ)/δ⌋+1 := by
    change ((Finset.Icc (0 : ℤ) ⌊(2 : ℝ)/δ⌋).card : ℤ) = _
    rw [Int.card_Icc_of_le 0 _ (by omega),sub_zero]
  have hReal : (I.card : ℝ) = (⌊(2 : ℝ)/δ⌋ : ℝ)+1 := by exact_mod_cast hInt
  calc
    _ ≤ (I.card : ℝ) := by exact_mod_cast hc
    _ ≤ _ := by rw [hReal]; linarith only [Int.floor_le ((2 : ℝ)/δ)]

end ArtinMatthews
