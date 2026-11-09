module

public import BridgeWeil


set_option backward.privateInPublic true
@[expose] public section

/-! The actual frozen prime Weil theorem, transferred to the original integer-frequency sum. -/
noncomputable section
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews.PrimePowerWeil

theorem standardSum_prime_weil_bound (p : ℕ) [Fact p.Prime] (h k : ℤ)
    (hnot : (h:ZMod p)≠0 ∨ (k:ZMod p)≠0) :
    ‖standardSum p h k‖≤2*Real.sqrt p := by
  have hb := unitKloostermanSum_prime_weil_bound p (h:ZMod p) (k:ZMod p) hnot
  rw [unitKloostermanSum_eq_standardSum] at hb
  simpa only [standardSum,Int.cast_natCast,ZMod.natCast_zmod_val] using hb

end ArtinMatthews.PrimePowerWeil
