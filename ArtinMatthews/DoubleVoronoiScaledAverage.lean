module

public import ArtinMatthews.DoubleVoronoiCongruenceAverage
public import OAI.NumberTheory.Jacobsthal.Harmonic.CharacterReduction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual q-character average reduces to the d-character residue
indicator by the proved standard-character reduction map. -/

namespace ArtinMatthews
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman.PrimePower
noncomputable section

/-- The normalized lifted congruence average, including its unscaled
Kloosterman phase, at the actual composite modulus H*d. -/
theorem doubleVoronoi_scaled_average (H d : ℕ) [NeZero H] [NeZero d]
    (v : (ZMod (H*d))ˣ) (k base : ZMod (H*d)) :
    (∑ j : ZMod d, ZMod.stdAddChar (base + (H : ZMod (H*d)) *
      (j.val : ZMod (H*d)) * (k*(↑v⁻¹ : ZMod (H*d))-(v : ZMod (H*d))))) / (d : ℂ) =
      ZMod.stdAddChar base *
        (if reduction H d k = (ZMod.unitsMap (dvd_mul_left d H) v : ZMod d)^2 then 1 else 0) := by
  classical
  let v' := ZMod.unitsMap (dvd_mul_left d H) v
  have hred : reduction H d (k*(↑v⁻¹ : ZMod (H*d))-(v : ZMod (H*d))) =
      reduction H d k*(↑v'⁻¹ : ZMod d)-(v' : ZMod d) := by
    simp [v', reduction, ZMod.unitsMap_def, ← map_inv]
  have hp (j : ZMod d) :
      ZMod.stdAddChar (base + (H : ZMod (H*d)) *
        (j.val : ZMod (H*d)) * (k*(↑v⁻¹ : ZMod (H*d))-(v : ZMod (H*d)))) =
      ZMod.stdAddChar base * ZMod.stdAddChar
        (j*(reduction H d k*(↑v'⁻¹ : ZMod d)-(v' : ZMod d))) := by
    rw [AddChar.map_add_eq_mul, mul_assoc, standard_character_reduction]
    rw [map_mul, map_natCast, ZMod.natCast_zmod_val, hred]
  simp_rw [hp]
  rw [← Finset.mul_sum, mul_div_assoc]
  congr 1
  have havg := inverse_linear_character_average
    (ZMod.stdAddChar (N := d)) (ZMod.isPrimitive_stdAddChar d) v' (reduction H d k)
  by_cases hk : reduction H d k = (v' : ZMod d)^2
  · simpa [ZMod.card, v', hk] using havg
  · simpa [ZMod.card, v', hk] using havg

end
end ArtinMatthews
