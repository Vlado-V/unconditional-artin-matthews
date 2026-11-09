module

public import ArtinMatthews.ProbeIdealPowerQuotients
public import Mathlib.Algebra.Group.AddChar


set_option backward.privateInPublic true
@[expose] public section

/-! Representative independence of the finite Poisson congruence kernel,
with arbitrary ideals; no principal-ideal hypothesis is needed. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open scoped BigOperators Classical
noncomputable section
variable {R : Type*} [CommRing R]

theorem probeIdealPoisson_gate_congr (I : Ideal R) (a h x x' : R)
    (hx : x - x' ∈ I) : (h - a * x ∈ I ↔ h - a * x' ∈ I) := by
  have he : h - a * x' = (h - a * x) + a * (x - x') := by ring
  constructor
  · intro hh
    rw [he]
    exact I.add_mem hh (I.mul_mem_left a hx)
  · intro hh
    have he' : h - a * x = (h - a * x') - a * (x - x') := by ring
    rw [he']
    exact I.sub_mem hh (I.mul_mem_left a hx)

theorem probeIdealPoisson_phase_congr (I J : Ideal R) (a h x x' y y' : R)
    (ha : a ∈ J) (hx : x - x' ∈ I) (hy : y - y' ∈ J) (hh : h - a * x ∈ I)
    (ψ : AddChar (R ⧸ (I * J)) ℂ) :
    ψ (Ideal.Quotient.mk _ ((h - a * x) * y)) =
      ψ (Ideal.Quotient.mk _ ((h - a * x') * y')) := by
  apply congrArg ψ
  apply Ideal.Quotient.eq.mpr
  have hfirst := Ideal.mul_mem_mul hh hy
  have hsecond : a * (x - x') * y' ∈ I * J :=
    (I * J).mul_mem_right y' (Ideal.mul_mem_mul_rev hx ha)
  convert (I * J).sub_mem hfirst hsecond using 1; ring

def probeIdealPoissonTerm (I J : Ideal R) (a h : R)
    (ψ : AddChar (R ⧸ (I * J)) ℂ) (W : (R ⧸ I) → ℂ) (V : (R ⧸ J) → ℂ)
    (d : R ⧸ I) (v : R ⧸ J) : ℂ :=
  if h - a * Quotient.out d ∈ I then W d * V v *
    ψ (Ideal.Quotient.mk _ ((h - a * Quotient.out d) * Quotient.out v)) else 0

theorem probeIdealPoissonTerm_mk (I J : Ideal R) (a h : R) (ha : a ∈ J)
    (ψ : AddChar (R ⧸ (I * J)) ℂ) (W : (R ⧸ I) → ℂ) (V : (R ⧸ J) → ℂ)
    (x y : R) :
    probeIdealPoissonTerm I J a h ψ W V (Ideal.Quotient.mk I x) (Ideal.Quotient.mk J y) =
      if h - a * x ∈ I then W (Ideal.Quotient.mk I x) * V (Ideal.Quotient.mk J y) *
        ψ (Ideal.Quotient.mk _ ((h - a * x) * y)) else 0 := by
  let d := Ideal.Quotient.mk I x
  let v := Ideal.Quotient.mk J y
  have hx : x - Quotient.out d ∈ I :=
    Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out d).symm
  have hy : y - Quotient.out v ∈ J :=
    Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out v).symm
  unfold probeIdealPoissonTerm
  have hg := probeIdealPoisson_gate_congr I a h x (Quotient.out d) hx
  by_cases hh : h - a * x ∈ I
  · rw [ite_eq_left hh, ite_eq_left (hg.mp hh)]
    rw [probeIdealPoisson_phase_congr I J a h x (Quotient.out d) y (Quotient.out v)
      ha hx hy hh ψ]
  · rw [ite_eq_right hh, ite_eq_right (fun hh' => hh (hg.mpr hh'))]

end
end ArtinMatthews.VaryingKummerAnalytic
