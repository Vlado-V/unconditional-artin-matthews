module

public import ArtinMatthews.SpectralInfinityReducedUnits
public import ArtinMatthews.KloostermanAllModulusWeil


set_option backward.privateInPublic true
@[expose] public section

/-! The actual infinity-cusp Kloosterman sum, at true width one, is the
proved ordinary all-modulus sum at N-divisible moduli and zero otherwise.
The reduction retains the literal phase and all frequency gcd factors. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups BigOperators
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

theorem gamma0TrueWidthKloostermanSum_identity_eq_unit (N : ℕ) [NeZero N]
    (c : ℕ) [NeZero c] (hNc : N ∣ c) (m n : ℤ) :
    gamma0TrueWidthKloostermanSum N 1 1 c m n = unitKloostermanSum c (m : ZMod c) (n : ZMod c) := by
  classical
  unfold gamma0TrueWidthKloostermanSum unitKloostermanSum doubleCharacterSum
  apply Fintype.sum_equiv (gamma0InfinityReducedUnitEquiv N c hNc)
  intro R
  rw [zmodAddEquiv_apply_eq_stdAddChar,zmodAddEquiv_apply_eq_stdAddChar,← AddChar.map_add_eq_mul]
  change cuspTrueWidthGeometricPhase N 1 1 m n c R.val =
    ZMod.stdAddChar ((m : ZMod c)*(R.val 1 1 : ZMod c)+(n : ZMod c)*(R.val 0 0 : ZMod c))
  rw [show (m : ZMod c)*(R.val 1 1 : ZMod c)+(n : ZMod c)*(R.val 0 0 : ZMod c) =
      (((m*R.val 1 1+n*R.val 0 0 : ℤ)) : ZMod c) by push_cast; rfl,stdAddChar_eq_atkinPhase]
  unfold cuspTrueWidthGeometricPhase
  simp only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul,Int.cast_natCast]
  congr 1
  push_cast
  ring_nf

theorem gamma0TrueWidthKloostermanSum_identity_eq_standard (N : ℕ) [NeZero N]
    (c : ℕ) [NeZero c] (m n : ℤ) :
    gamma0TrueWidthKloostermanSum N 1 1 c m n = if N ∣ c then standardSum c m n else 0 := by
  by_cases hNc : N ∣ c
  · rw [ite_eq_left hNc,gamma0TrueWidthKloostermanSum_identity_eq_unit N c hNc,
      unitKloostermanSum_eq_standardSum]
    unfold standardSum
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  · let _ : IsEmpty (gamma0TrueWidthReducedMatrix N 1 1 c) :=
      ⟨fun R => hNc (gamma0TrueWidthReducedMatrix_identity_dvd N c R)⟩
    simp only [ite_eq_right hNc,gamma0TrueWidthKloostermanSum,Finset.univ_eq_empty,Finset.sum_empty]

theorem gamma0TrueWidthKloostermanSum_identity_weil {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N c : ℕ) [NeZero N] [NeZero c] (m n : ℤ),
      ‖gamma0TrueWidthKloostermanSum N 1 1 c m n‖ ≤
        C*(c : ℝ)^((1/2 : ℝ)+ε)*((Nat.gcd c (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) := by
  obtain ⟨C,hC,hW⟩ := standardKloosterman_weil_bound hε
  refine ⟨C,hC,?_⟩
  intro N c _ _ m n
  rw [gamma0TrueWidthKloostermanSum_identity_eq_standard]
  by_cases hNc : N ∣ c
  · rw [ite_eq_left hNc]
    exact hW c m n
  · rw [ite_eq_right hNc,norm_zero]
    positivity

end ArtinMatthews
