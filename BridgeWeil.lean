module

public import ArtinMatthews.KloostermanWeakBound
public import rml.weil.contracts


set_option backward.privateInPublic true
@[expose] public section

/-! Exact reuse of Charlie Dorsey's Weil Bounds Toolkit at commit
0f3e4c3010bb0e7c4e514ddb5bd3a0a0e082bf68 (Apache-2.0).
The finite sum is identified before any estimate is transferred. -/

namespace ArtinMatthews

open scoped BigOperators

theorem unitKloostermanSum_eq_weilToolkit (N : ℕ) [NeZero N]
    (h k : ZMod N) :
    unitKloostermanSum N h k = RML.ExpSum.Weil.kloostermanUnitSum N k h := by
  classical
  unfold unitKloostermanSum doubleCharacterSum RML.ExpSum.Weil.kloostermanUnitSum
  apply Finset.sum_congr rfl
  intro u _
  rw [zmodAddEquiv_apply_eq_stdAddChar, zmodAddEquiv_apply_eq_stdAddChar,
    ← AddChar.map_add_eq_mul]

theorem unitKloostermanSum_prime_weil_bound (p : ℕ) [Fact p.Prime]
    (h k : ZMod p) (hnot : h ≠ 0 ∨ k ≠ 0) :
    ‖unitKloostermanSum p h k‖ ≤ 2 * Real.sqrt p := by
  rw [unitKloostermanSum_eq_weilToolkit]
  exact RML.ExpSum.Weil.kloostermanUnitSum_prime_le_two_sqrt_of_not_both_zero
    RML.ExpSum.Weil.prime_bound p k h hnot.symm

theorem unitKloostermanSum_squarefree_weil_bound_right
    {q : ℕ} [NeZero q] (hsq : Squarefree q)
    (h k : ZMod q) (hk : IsUnit k) :
    ‖unitKloostermanSum q h k‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * Real.sqrt q := by
  rw [unitKloostermanSum_eq_weilToolkit]
  exact RML.ExpSum.Weil.squarefreeUnitNumerator_bound hsq k h hk

end ArtinMatthews
