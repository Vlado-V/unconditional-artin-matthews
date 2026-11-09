module

public import ArtinMatthews.SpectralMixedCuspExceptionalBessel
public import ArtinMatthews.SpectralKloostermanDiagonalWeilSum


set_option backward.privateInPublic true
@[expose] public section

/-! The actual true-width exceptional singleton has the square-root
Weil cutoff. The ABL height substitution is literal. -/

noncomputable section
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0MixedCusp_exceptional_singleton_weil {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s],
      r.Coprime s → ∀ (u : Finset (Gamma0AllHeightSpectralIndex (r*s))) (n : ℤ) (hn : n ≠ 0)
      {A Y : ℝ}, 0 < A → 2*A ≤ 1 → ∀ hY : 0 < Y,
      Y < A/(|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ i ∈ u, gamma0AllHeightGradientSpectralValue (r*s) i ≤ 1/4) →
      let Q := |cuspFourierFrequency 1 n|/A
      (Real.exp (-Real.exp 1)/16)^2*gamma0CuspExceptionalMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn A ≤
        1+8*D*Q^ε*(n.natAbs.divisors.card : ℝ)*Real.sqrt (Nat.gcd (r*s) n.natAbs : ℝ)*
          Real.sqrt Q/((r*s : ℕ) : ℝ) := by
  obtain ⟨D,hD,hWeil⟩ := spectralKloostermanDiagSum_weil hε
  refine ⟨D,hD,?_⟩
  intro r s instR instS hcop u n hn A Y hA hA₁ hY hYA heig
  dsimp only
  let N := r*s
  let Q := |cuspFourierFrequency 1 n|/A
  have hQ : 0 < Q :=
    div_pos (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)) hA
  have h := gamma0MixedCusp_exceptional_singleton_compact_bound r s hcop u n hn hA hA₁ hY hYA heig
  refine h.trans ?_
  calc
    _ ≤ 1+8*(D*Q^ε*(n.natAbs.divisors.card : ℝ)*Real.sqrt (Nat.gcd N n.natAbs : ℝ)*
        Real.sqrt Q/(N : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hWeil N n hn Q hQ) (by norm_num : (0 : ℝ) ≤ 8))
    _ = _ := by dsimp only [N,Q]; ring

theorem spectralExceptionalABLWeight_eq (X Z ν : ℝ) (hXZ : 0 ≤ X/Z) :
    ((X/Z)^2)^(-2*ν) = (X/Z)^(-4*ν) := by
  rw [← Real.rpow_natCast_mul hXZ]
  congr 1
  push_cast
  ring

theorem gamma0MixedCusp_exceptional_singleton_abl_height {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s],
      r.Coprime s → ∀ (u : Finset (Gamma0AllHeightSpectralIndex (r*s))) (n : ℤ) (hn : n ≠ 0)
      {X Z Y : ℝ}, 0 < X → 0 < Z → 2*(X/Z)^2 ≤ 1 → ∀ hY : 0 < Y,
      Y < (X/Z)^2/(|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ i ∈ u, gamma0AllHeightGradientSpectralValue (r*s) i ≤ 1/4) →
      let Q := |cuspFourierFrequency 1 n|/(X/Z)^2
      (Real.exp (-Real.exp 1)/16)^2*
        gamma0CuspExceptionalMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn ((X/Z)^2) ≤
        1+8*D*Q^ε*(n.natAbs.divisors.card : ℝ)*Real.sqrt (Nat.gcd (r*s) n.natAbs : ℝ)*
          Real.sqrt Q/((r*s : ℕ) : ℝ) := by
  obtain ⟨D,hD,hWeil⟩ := gamma0MixedCusp_exceptional_singleton_weil hε
  refine ⟨D,hD,?_⟩
  intro r s instR instS hcop u n hn X Z Y hX hZ hSmall hY hYA heig
  exact hWeil r s hcop u n hn (sq_pos_of_pos (div_pos hX hZ)) hSmall hY hYA heig

end ArtinMatthews
