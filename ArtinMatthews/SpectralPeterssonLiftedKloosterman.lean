module

public import ArtinMatthews.SpectralCuspWidthCharacters
public import ArtinMatthews.KloostermanAllModulusWeil


set_option backward.privateInPublic true
@[expose] public section

/-! A congruence-masked lift of the right diagonal, with its exact finite Fourier expansion. -/

noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

/-- The integer representative of a residue and its common-period lift. -/
def peterssonResidueLift {N c : ℕ} (d : ZMod c) (j : Fin N) : ℤ :=
  (d.val : ℤ) + (c : ℤ) * j.val

def peterssonLiftedKloostermanSum (N c : ℕ) [NeZero c] (a b h m : ℤ) : ℂ :=
  ∑ u : (ZMod c)ˣ, ∑ j : Fin N,
    if (N : ℤ) ∣ (c : ℤ) * a + peterssonResidueLift u.val j * b then
      atkinPhase ((h : ℝ) * (peterssonResidueLift u.val j : ℝ) / ((N : ℝ) * c) +
        (m : ℝ) * (u⁻¹).val.val / c)
    else 0

/-- Frequency of the right diagonal after inserting one congruence character. -/
def peterssonLiftedFrequency {N : ℕ} (c : ℕ) (b h : ℤ) (k : Fin N) : ℤ :=
  h + (k.val : ℤ) * b * c

theorem peterssonCongruenceMask_eq_fourier (N : ℕ) [NeZero N] (z : ℤ) :
    (if (N : ℤ) ∣ z then (1 : ℂ) else 0) =
      (N : ℂ)⁻¹ * ∑ k : Fin N, atkinPhase ((z : ℝ) * k.val / N) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [sum_fin_atkinPhase_int_ratio N (NeZero.pos N) z]
  by_cases hz : (N : ℤ) ∣ z <;> simp [hz, hN]

private theorem standardSum_eq_atkinPhases (c : ℕ) [NeZero c] (h m : ℤ) :
    standardSum c h m =
      ∑ u : (ZMod c)ˣ,
        atkinPhase ((h : ℝ) * u.val.val / c + (m : ℝ) * (u⁻¹).val.val / c) := by
  rw [standardSum_exp]
  apply Finset.sum_congr rfl
  intro u _
  unfold atkinPhase
  congr 1
  push_cast
  ring

theorem peterssonLiftedKloostermanSum_eq_standardSum (N c : ℕ) [NeZero N] [NeZero c]
    (a b h m : ℤ) :
    peterssonLiftedKloostermanSum N c a b h m =
      ∑ k : Fin N, if (N : ℤ) ∣ peterssonLiftedFrequency c b h k then
        atkinPhase ((k.val : ℝ) * c * a / N) *
          standardSum c m (peterssonLiftedFrequency c b h k / (N : ℤ))
      else 0 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  let A (k : Fin N) : ℂ := atkinPhase ((k.val : ℝ) * c * a / N)
  let B (k : Fin N) (u : (ZMod c)ˣ) : ℂ :=
    atkinPhase ((peterssonLiftedFrequency c b h k : ℝ) * u.val.val / ((N : ℝ) * c) +
      (m : ℝ) * (u⁻¹).val.val / c)
  let term (u : (ZMod c)ˣ) (j k : Fin N) : ℂ :=
    ((N : ℂ)⁻¹ * (A k * B k u)) *
      atkinPhase ((peterssonLiftedFrequency c b h k : ℝ) * j.val / N)
  have hterm (u : (ZMod c)ˣ) (j : Fin N) :
      (if (N : ℤ) ∣ (c : ℤ) * a + peterssonResidueLift u.val j * b then
        atkinPhase ((h : ℝ) * (peterssonResidueLift u.val j : ℝ) / ((N : ℝ) * c) +
          (m : ℝ) * (u⁻¹).val.val / c)
      else 0) = ∑ k : Fin N, term u j k := by
    let z : ℤ := (c : ℤ) * a + peterssonResidueLift u.val j * b
    let x : ℝ := (h : ℝ) * (peterssonResidueLift u.val j : ℝ) / ((N : ℝ) * c) +
      (m : ℝ) * (u⁻¹).val.val / c
    change (if (N : ℤ) ∣ z then atkinPhase x else 0) = _
    calc
      _ = ((N : ℂ)⁻¹ * ∑ k : Fin N, atkinPhase ((z : ℝ) * k.val / N)) *
          atkinPhase x := by
        rw [← peterssonCongruenceMask_eq_fourier N z]
        split <;> simp
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        have hphase :
            (z : ℝ) * k.val / N + x =
              (k.val : ℝ) * c * a / N +
              ((peterssonLiftedFrequency c b h k : ℝ) * u.val.val / ((N : ℝ) * c) +
                (m : ℝ) * (u⁻¹).val.val / c) +
              (peterssonLiftedFrequency c b h k : ℝ) * j.val / N := by
          dsimp [z, x, peterssonLiftedFrequency, peterssonResidueLift]
          push_cast
          field_simp [hN, hc]
          ring
        dsimp only [term, A, B]
        rw [mul_assoc, ← atkinPhase_add, hphase, atkinPhase_add, atkinPhase_add]
        ring
  have hj (u : (ZMod c)ˣ) (k : Fin N) :
      (∑ j : Fin N, term u j k) =
        if (N : ℤ) ∣ peterssonLiftedFrequency c b h k then A k * B k u else 0 := by
    dsimp only [term]
    rw [← Finset.mul_sum, sum_fin_atkinPhase_int_ratio N (NeZero.pos N)]
    by_cases hd : (N : ℤ) ∣ peterssonLiftedFrequency c b h k
    · rw [ite_eq_left hd, ite_eq_left hd, mul_comm ((N : ℂ)⁻¹), mul_assoc, inv_mul_cancel₀ hNC, mul_one]
    · simp [hd]
  unfold peterssonLiftedKloostermanSum
  simp_rw [hterm]
  calc
    _ = ∑ u : (ZMod c)ˣ, ∑ k : Fin N, ∑ j : Fin N, term u j k := by
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.sum_comm
    _ = ∑ k : Fin N, ∑ u : (ZMod c)ˣ, ∑ j : Fin N, term u j k := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [hj]
      by_cases hd : (N : ℤ) ∣ peterssonLiftedFrequency c b h k
      · simp only [ite_eq_left hd, ← Finset.mul_sum]
        change A k * (∑ u : (ZMod c)ˣ, B k u) =
          A k * standardSum c m (peterssonLiftedFrequency c b h k / (N : ℤ))
        congr 1
        let t : ℤ := peterssonLiftedFrequency c b h k / (N : ℤ)
        have ht : (t : ℝ) * (N : ℝ) = (peterssonLiftedFrequency c b h k : ℝ) := by
          exact_mod_cast Int.ediv_mul_cancel hd
        have hswap : standardSum c m t = standardSum c t m :=
          sum_swap ZMod.stdAddChar (m : ZMod c) (t : ZMod c)
        change (∑ u : (ZMod c)ˣ, B k u) = standardSum c m t
        rw [hswap, standardSum_eq_atkinPhases]
        apply Finset.sum_congr rfl
        intro u _
        dsimp only [B]
        congr 1
        rw [← ht]
        field_simp [hN, hc]
      · simp [hd]

end ArtinMatthews
