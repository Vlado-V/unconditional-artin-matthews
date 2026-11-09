module

public import ArtinMatthews.SpectralCuspTwoCellFourier
public import ArtinMatthews.SpectralHorizontalPeriodPartition


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact horizontal window sums to one under every integer
multiple of its period.  No period-one normalization is introduced. -/

noncomputable section
open Set
open scoped BigOperators

namespace ArtinMatthews

theorem spectralHorizontalPartition_finsum_on_period {w x : ℝ} (hw : 0 < w)
    (hx : x ∈ Icc 0 w) :
    (∑ᶠ k : ℤ, spectralHorizontalPartition w (x + w * k)) = 1 := by
  classical
  have hs : Function.support (fun k : ℤ => spectralHorizontalPartition w (x + w * k)) ⊆
      ({0,1} : Finset ℤ) := by
    intro k hk
    by_contra hnot
    have hki : k ≤ -1 ∨ 2 ≤ k := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hnot
      omega
    change spectralHorizontalPartition w (x + w * k) ≠ 0 at hk
    rcases hki with hki | hki
    · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hki
      exact hk (spectralHorizontalPartition_zero_left hw (by nlinarith [hx.2]))
    · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hki
      exact hk (spectralHorizontalPartition_zero_right hw (by nlinarith [hx.1]))
  calc
    _ = spectralHorizontalPartition w x + spectralHorizontalPartition w (x + w) := by
      rw [finsum_eq_sum_of_support_subset _ hs]
      simp
    _ = 1 := spectralHorizontalPartition_add_shift hw hx

theorem spectralHorizontalPartition_lattice_finsum {w : ℝ} (hw : 0 < w) (x : ℝ) :
    (∑ᶠ k : ℤ, spectralHorizontalPartition w (x + w * k)) = 1 := by
  let k : ℤ := Int.floor (x / w)
  let y : ℝ := x - w * k
  have hklo : (k : ℝ) ≤ x / w := Int.floor_le _
  have hkhi : x / w < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hy : y ∈ Icc 0 w := by
    constructor
    · have h := (le_div_iff₀ hw).mp hklo
      dsimp [y]
      nlinarith
    · have h := (div_lt_iff₀ hw).mp hkhi
      dsimp [y]
      nlinarith
  calc
    _ = ∑ᶠ j : ℤ, spectralHorizontalPartition w (y + w * (j + k)) := by
      congr 1
      funext j
      congr 1
      dsimp [y]
      ring
    _ = ∑ᶠ j : ℤ, spectralHorizontalPartition w (y + w * j) := by
      simpa using (finsum_comp_equiv
        (f := fun j : ℤ => spectralHorizontalPartition w (y + w * j)) (Equiv.addRight k))
    _ = 1 := spectralHorizontalPartition_finsum_on_period hw hy

end ArtinMatthews
