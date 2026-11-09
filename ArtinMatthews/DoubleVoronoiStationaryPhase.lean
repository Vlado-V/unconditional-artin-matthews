module

public import ArtinMatthews.KloostermanStationaryReduction
public import ArtinMatthews.KloostermanStationaryCongruence


set_option backward.privateInPublic true
@[expose] public section

/-! Exact conversion of the stationary phase to the integral congruence
used by the double Voronoi formula. -/
namespace ArtinMatthews
open OAI.Erdos970.ErdosKloosterman.PrimePower

variable {R : Type*} [CommRing R]

theorem stationary_phase_unit_equation (v : Rˣ) (a b : R) :
    a-b*(↑v⁻¹ : R)=0 ↔ a*(v : R)=b := by
  rw [sub_eq_zero]
  constructor
  · intro h
    simpa only [mul_assoc, Units.inv_mul, mul_one] using
      congrArg (fun x : R => x*(v : R)) h
  · intro h
    simpa only [mul_assoc, Units.mul_inv, mul_one] using
      congrArg (fun x : R => x*(↑v⁻¹ : R)) h

/-- The reciprocal Kloosterman parameter is removed by multiplication by
units; this is valid over the composite quotient ring. -/
theorem doubleVoronoi_stationary_equation (m₃ m₄ u : Rˣ) (k₁ k₂ : R) :
    (m₃ : R)-(m₄ : R)-(↑(m₃*m₄)⁻¹ : R)*
        ((m₄ : R)*k₂-(m₃ : R)*k₁)*(↑u⁻¹ : R)^2=0 ↔
      ((m₃ : R)-(m₄ : R))*(m₃ : R)*(m₄ : R)*(u : R)^2 =
        (m₄ : R)*k₂-(m₃ : R)*k₁ := by
  convert stationary_phase_unit_equation (m₃*m₄*u^2)
    ((m₃ : R)-(m₄ : R)) ((m₄ : R)*k₂-(m₃ : R)*k₁) using 1 <;>
    simp only [pow_two, mul_inv_rev, Units.val_mul] <;>
    ring_nf

/-- The actual stationary support for shift q/D is precisely the
polynomial congruence modulo D. -/
theorem doubleVoronoi_stationary_support {q D : ℕ} [NeZero q]
    (hq : 0<q) (hDq : D∣q) (m₃ m₄ u : (ZMod q)ˣ) (k₁ k₂ : ZMod q) :
    u ∈ stationaryUnits ((q/D : ℕ) : ZMod q)
      ((m₃ : ZMod q)-(m₄ : ZMod q))
      ((↑(m₃*m₄)⁻¹ : ZMod q)*((m₄ : ZMod q)*k₂-(m₃ : ZMod q)*k₁)) ↔
    let f := ZMod.castHom hDq (ZMod D)
    ((f (m₃ : ZMod q))-(f (m₄ : ZMod q)))*f (m₃ : ZMod q)*
      f (m₄ : ZMod q)*(f (u : ZMod q))^2 =
        f (m₄ : ZMod q)*f k₂-f (m₃ : ZMod q)*f k₁ := by
  rw [stationaryUnits_quotient_iff hq hDq]
  simp only [map_sub, map_mul, map_pow]
  let f := ZMod.castHom hDq (ZMod D)
  have hprod : (↑((ZMod.unitsMap hDq m₃)*(ZMod.unitsMap hDq m₄))⁻¹ : ZMod D) =
      f (↑(m₃*m₄)⁻¹ : ZMod q) := by
    rw [← map_mul]
    rfl
  have hx := doubleVoronoi_stationary_equation (ZMod.unitsMap hDq m₃)
      (ZMod.unitsMap hDq m₄) (ZMod.unitsMap hDq u) (f k₁) (f k₂)
  rw [hprod] at hx
  simpa only [f, ZMod.unitsMap_def, Units.coe_map, Units.coe_map_inv,
    MonoidHom.coe_ofClass] using hx

end ArtinMatthews
