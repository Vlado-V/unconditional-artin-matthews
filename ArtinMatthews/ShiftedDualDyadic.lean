module

public import ArtinMatthews.SpectralDyadicReassembly
public import ArtinMatthews.ShiftedDualSplit


set_option backward.privateInPublic true
@[expose] public section

/-! Exact, absolutely convergent dyadic reassembly of the nonzero-frequency
Kloosterman dual. No cancellation estimate is assumed in this decomposition. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators

lemma shiftedDualNonzeroTerm_fst_pos (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha0 : a 0 = 0) (k : ℕ × ℕ)
    (hk : shiftedDualNonzeroTerm q D m3 m4 a b k ≠ 0) : 1 ≤ k.1 := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  apply hk
  simp [shiftedDualNonzeroTerm, shiftedDualTerm, h, ha0]

lemma shiftedDualNonzeroTerm_snd_pos (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (hb0 : b 0 = 0) (k : ℕ × ℕ)
    (hk : shiftedDualNonzeroTerm q D m3 m4 a b k ≠ 0) : 1 ≤ k.2 := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  apply hk
  simp [shiftedDualNonzeroTerm, shiftedDualTerm, h, hb0]

theorem shiftedDualNonzero_dyadic_summable (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    Summable (fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
      spectralDyadicCoefficient (shiftedDualNonzeroTerm q D m3 m4 a b z.1)
        z.1.1 z.1.2 z.2) :=
  spectralDyadic_expansion_summable _ Prod.fst Prod.snd
    (shiftedDualNonzeroTerm_summable q D m3 m4 a b ha hb)
    (shiftedDualNonzeroTerm_fst_pos q D m3 m4 a b ha0)
    (shiftedDualNonzeroTerm_snd_pos q D m3 m4 a b hb0)

theorem shiftedDualNonzero_dyadic_reassembly (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    (∑' k, shiftedDualNonzeroTerm q D m3 m4 a b k) =
      ∑' d : ℕ × ℕ, ∑' k : ℕ × ℕ,
        spectralDyadicCoefficient (shiftedDualNonzeroTerm q D m3 m4 a b k)
          k.1 k.2 d :=
  spectralDyadic_reassembly _ Prod.fst Prod.snd
    (shiftedDualNonzeroTerm_summable q D m3 m4 a b ha hb)
    (shiftedDualNonzeroTerm_fst_pos q D m3 m4 a b ha0)
    (shiftedDualNonzeroTerm_snd_pos q D m3 m4 a b hb0)

theorem shiftedDualNonzero_dyadic_norm (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    (∑' z : (ℕ × ℕ) × (ℕ × ℕ),
      ‖spectralDyadicCoefficient (shiftedDualNonzeroTerm q D m3 m4 a b z.1)
        z.1.1 z.1.2 z.2‖) = ∑' k, ‖shiftedDualNonzeroTerm q D m3 m4 a b k‖ :=
  spectralDyadic_norm_reassembly _ Prod.fst Prod.snd
    (shiftedDualNonzeroTerm_summable q D m3 m4 a b ha hb)
    (shiftedDualNonzeroTerm_fst_pos q D m3 m4 a b ha0)
    (shiftedDualNonzeroTerm_snd_pos q D m3 m4 a b hb0)

end ArtinMatthews
