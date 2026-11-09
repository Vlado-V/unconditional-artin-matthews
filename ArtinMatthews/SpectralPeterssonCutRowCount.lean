module

public import ArtinMatthews.SpectralPeterssonCutRows


set_option backward.privateInPublic true
@[expose] public section

/-! The actual parabolic cut rows have the sharp uniform congruence-level
count, independently of the holomorphic weight. -/
noncomputable section
open Set
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0PeterssonHeightRows_card_le (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (z : UpperHalfPlane) (A : ℝ) (hA : 0 < A)
    (T : Finset (Gamma0PeterssonSignedRow N 1 a))
    (hT : ∀ p ∈ T, A ≤ gamma0PeterssonRowHeight N a p z) :
    T.card ≤ (cuspEisensteinHeightRows N a z ((gamma0CuspTrueWidth N a : ℝ)*A)
      (mul_pos (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)) hA)).card := by
  classical
  let e : Gamma0PeterssonSignedRow N 1 a ↪ Gamma0CuspEisensteinRows N 1 a :=
    ⟨gamma0PeterssonEisensteinRow N a,gamma0PeterssonEisensteinRow_injective N a⟩
  have hw : 0 < (gamma0CuspTrueWidth N a : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hsub : T.map e ⊆ cuspEisensteinHeightRows N a z ((gamma0CuspTrueWidth N a : ℝ)*A)
      (mul_pos hw hA) := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hv
    rw [cuspEisensteinHeightRows_mem]
    have h := hT p hp
    rw [gamma0PeterssonRowHeight_eq] at h
    have hh := (le_div_iff₀ hw).mp h
    simpa only [e,mul_comm] using! hh
  simpa only [Finset.card_map] using Finset.card_le_card hsub

theorem gamma0PeterssonHeightRows_infinity_card (N : ℕ) [NeZero N]
    (z : UpperHalfPlane) (A : ℝ) (hA : 0 < A)
    (T : Finset (Gamma0PeterssonSignedRow N 1 1))
    (hT : ∀ p ∈ T, A ≤ gamma0PeterssonRowHeight N 1 p z) :
    (T.card : ℝ) ≤ 4*(1+2/((N : ℝ)*A)) := by
  have h := gamma0PeterssonHeightRows_card_le N 1 z A hA T hT
  have hc := gamma0Infinity_heightRows_card_le N z hA
  have he : (T.card : ℝ) ≤ ((cuspEisensteinHeightRows N 1 z A hA).card : ℝ) := by
    exact_mod_cast (by simpa only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul] using h)
  exact he.trans hc

theorem gamma0PeterssonHeightRows_mixed_card (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (z : UpperHalfPlane) (A : ℝ) (hA : 0 < A)
    (T : Finset (Gamma0PeterssonSignedRow (r*s) 1 (gamma0CuspOneOver s)))
    (hT : ∀ p ∈ T, A ≤ gamma0PeterssonRowHeight (r*s) (gamma0CuspOneOver s) p z) :
    (T.card : ℝ) ≤ 4*(1+2/(((r*s : ℕ) : ℝ)*A)) := by
  have h := gamma0PeterssonHeightRows_card_le (r*s) (gamma0CuspOneOver s) z A hA T hT
  have hc := gamma0MixedCusp_heightRows_card_le r s hcop z hA
  exact (show (T.card : ℝ) ≤ _ by exact_mod_cast h).trans hc

end ArtinMatthews
