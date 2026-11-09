module

public import ArtinMatthews.KloostermanWeightedStationary
public import ArtinMatthews.ShiftedVoronoiNumerators


set_option backward.privateInPublic true
@[expose] public section

/-! The finite-ring stationary equation for shift q/D is precisely a
congruence modulo D. -/

namespace ArtinMatthews
open OAI.Erdos970.ErdosKloosterman.PrimePower

/-- Multiplication by q/D embeds the additive quotient modulo D into
Z/qZ, expressed as an exact kernel identity. -/
theorem zmod_mul_quotient_eq_zero_iff {q D : ℕ} (hq : 0 < q) (hDq : D ∣ q)
    (x : ZMod q) :
    ((q/D : ℕ) : ZMod q)*x = 0 ↔ ZMod.castHom hDq (ZMod D) x = 0 := by
  have : NeZero q := ⟨by omega⟩
  have hD : 0 < D := Nat.pos_of_dvd_of_pos hDq hq
  have hquot : 0 < q/D := Nat.div_pos (Nat.le_of_dvd hq hDq) hD
  have hdvd : q ∣ (q/D)*x.val ↔ D ∣ x.val := by
    calc
      q ∣ (q/D)*x.val ↔ (q/D)*D ∣ (q/D)*x.val := by rw [Nat.div_mul_cancel hDq]
      _ ↔ D ∣ x.val := Nat.mul_dvd_mul_iff_left hquot
  have hx : (x.val : ZMod q) = x := ZMod.natCast_zmod_val x
  have hright : ZMod.castHom hDq (ZMod D) x = (x.val : ZMod D) := by
    calc
      _ = ZMod.castHom hDq (ZMod D) (x.val : ZMod q) := congrArg _ hx.symm
      _ = _ := map_natCast _ _
  rw [hright, ZMod.natCast_eq_zero_iff]
  rw [← hdvd]
  nth_rw 1 [← hx]
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]

/-- Exact stationary support at modulus D for an arbitrary pair of
Kloosterman arguments. -/
theorem stationaryUnits_quotient_iff {q D : ℕ} [NeZero q] (hq : 0 < q) (hDq : D ∣ q)
    (a b : ZMod q) (u : (ZMod q)ˣ) :
    u ∈ stationaryUnits ((q/D : ℕ) : ZMod q) a b ↔
      ZMod.castHom hDq (ZMod D) (a-b*(↑u⁻¹ : ZMod q)^2) = 0 := by
  classical
  simp only [stationaryUnits, Finset.mem_filter, Finset.mem_univ, true_and]
  exact zmod_mul_quotient_eq_zero_iff hq hDq _

end ArtinMatthews
