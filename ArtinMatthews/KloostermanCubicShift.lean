module

public import OAI.NumberTheory.Jacobsthal.Harmonic.StationaryPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact second-order unit and phase expansions for a cube-zero translation. -/
noncomputable section
namespace ArtinMatthews.PrimePowerWeil

variable {R : Type*} [CommRing R]

theorem cubicShift_mul_inverse (u : Rˣ) (t : R) (ht : t^3=0) :
    ((u:R)+t)*((↑u⁻¹:R)-t*(↑u⁻¹:R)^2+t^2*(↑u⁻¹:R)^3)=1 := by
  calc
    _ = (u:R)*↑u⁻¹ + t*↑u⁻¹*(1-(u:R)*↑u⁻¹) -
        t^2*(↑u⁻¹:R)^2*(1-(u:R)*↑u⁻¹)+t^3*(↑u⁻¹:R)^3 := by ring
    _ = 1 := by simp [ht]

def cubicShiftUnit (u : Rˣ) (t : R) (ht : t^3=0) : Rˣ :=
  Units.mkOfMulEqOne ((u:R)+t)
    ((↑u⁻¹:R)-t*(↑u⁻¹:R)^2+t^2*(↑u⁻¹:R)^3) (cubicShift_mul_inverse u t ht)

@[simp] theorem cubicShiftUnit_val (u : Rˣ) (t : R) (ht : t^3=0) :
    (cubicShiftUnit u t ht:R)=(u:R)+t := rfl

@[simp] theorem cubicShiftUnit_inv_val (u : Rˣ) (t : R) (ht : t^3=0) :
    (↑(cubicShiftUnit u t ht)⁻¹:R)=(↑u⁻¹:R)-t*(↑u⁻¹:R)^2+t^2*(↑u⁻¹:R)^3 := rfl

def cubicShiftEquiv (t : R) (ht : t^3=0) : Rˣ ≃ Rˣ where
  toFun u := cubicShiftUnit u t ht
  invFun u := cubicShiftUnit u (-t) (by
    calc
      (-t)^3= -t^3 := by ring
      _=0 := by rw [ht,neg_zero])
  left_inv u := by apply Units.ext; simp
  right_inv u := by apply Units.ext; simp

theorem cubicShift_phase (a b : R) (u : Rˣ) (t : R) (ht : t^3=0) :
    a*(cubicShiftUnit u t ht:R)+b*(↑(cubicShiftUnit u t ht)⁻¹:R) =
      a*(u:R)+b*(↑u⁻¹:R)+t*(a-b*(↑u⁻¹:R)^2)+t^2*(b*(↑u⁻¹:R)^3) := by
  rw [cubicShiftUnit_val,cubicShiftUnit_inv_val]
  ring

theorem cubicShift_stationary_quadratic (q a b : R) (u : Rˣ) (t : R)
    (ht : t^3=0) (hqt : q*t=0) :
    q*(a*(cubicShiftUnit u t ht:R)^2-b)=q*(a*(u:R)^2-b) := by
  rw [cubicShiftUnit_val]
  calc
    _ = q*(a*(u:R)^2-b)+(q*t)*(2*a*(u:R)+a*t) := by ring
    _ = _ := by rw [hqt,zero_mul,add_zero]

end ArtinMatthews.PrimePowerWeil
