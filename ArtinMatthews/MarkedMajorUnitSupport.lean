module

public import ArtinMatthews.MarkedMajorLabelSupportedEndpoint
public import ArtinMatthews.RoughCharacterPrimes


set_option backward.privateInPublic true
@[expose] public section

/-! Actual unit support for the six-character major-arc expansion. The
centered coefficient is treated literally as prime minus normalized rough. -/
namespace ArtinMatthews
open Finset

theorem marked_centered_nonzero_coprime {q n : ℕ} [NeZero q]
    (W modulation : ℝ) (hq : (q:ℝ) ≤ W) (hn : W < (n:ℝ))
    (hcoeff : markedMajorCenteredCoefficient W modulation n ≠ 0) : n.Coprime q := by
  classical
  by_cases hp : n.Prime
  · exact Nat.coprime_of_lt_prime (NeZero.ne q) (by exact_mod_cast hq.trans_lt hn) hp
  · have hav : ∀ p ∈ Nat.primesLE ⌊W⌋₊,¬p∣n := by
      by_contra h
      simp [markedMajorCenteredCoefficient,hp,h] at hcoeff
    exact rough_avoid_coprime _ (rough_primesLE_covers_modulus W hq) hav

theorem marked_centered_nonzero_isUnit {q n : ℕ} [NeZero q]
    (W modulation : ℝ) (hq : (q:ℝ) ≤ W) (hn : W < (n:ℝ))
    (hcoeff : markedMajorCenteredCoefficient W modulation n ≠ 0) : IsUnit (n:ZMod q) :=
  (ZMod.isUnit_iff_coprime n q).mpr (marked_centered_nonzero_coprime W modulation hq hn hcoeff)

theorem marked_label_coprime {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    {q : ℕ} [NeZero q] (hq : ∀ j p,p ∈ bands j → q < p)
    {s : ℕ} (hs : s ∈ markedMajorLabelSet bands) : s.Coprime q := by
  classical
  obtain ⟨t,_,rfl⟩ := mem_image.mp hs
  unfold markedPrimeBandProduct
  exact Nat.coprime_prod_left_iff.mpr (fun j _ =>
    Nat.coprime_of_lt_prime (NeZero.ne q) (hq j _ (t j).property) (hbands j _ (t j).property))

theorem marked_label_isUnit {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    {q : ℕ} [NeZero q] (hq : ∀ j p,p ∈ bands j → q < p)
    {s : ℕ} (hs : s ∈ markedMajorLabelSet bands) : IsUnit (s:ZMod q) :=
  (ZMod.isUnit_iff_coprime s q).mpr (marked_label_coprime bands hbands hq hs)

theorem marked_rough_isUnit {q n : ℕ} [NeZero q]
    (W : ℝ) (hq : (q:ℝ) ≤ W)
    (hn : ∀ p ∈ Nat.primesLE ⌊W⌋₊,¬p∣n) : IsUnit (n:ZMod q) :=
  (ZMod.isUnit_iff_coprime n q).mpr (rough_avoid_coprime _ (rough_primesLE_covers_modulus W hq) hn)

end ArtinMatthews
