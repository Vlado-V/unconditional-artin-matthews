module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic
public import Lean.Elab.Tactic.Omega


set_option backward.privateInPublic true
@[expose] public section

/-! Exterior valuations of genuine principal fractional ideals. Reduced
rows have valuations zero through five outside an arbitrary finite set S;
a sixth-power ratio of two such rows has an exterior S-unit root. -/
namespace ArtinMatthews
open IsDedekindDomain
open scoped NumberField nonZeroDivisors
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def exteriorPrincipalValuation (p : HeightOneSpectrum (𝓞 K)) (u : Kˣ) : ℤ :=
  FractionalIdeal.count K p (toPrincipalIdeal (𝓞 K) K u : FractionalIdeal (𝓞 K)⁰ K)

@[simp] theorem exteriorPrincipalValuation_one (p : HeightOneSpectrum (𝓞 K)) :
    exteriorPrincipalValuation p (1 : Kˣ)=0 := by
  unfold exteriorPrincipalValuation
  rw [map_one,Units.val_one,FractionalIdeal.count_one]

theorem exteriorPrincipalValuation_mul (p : HeightOneSpectrum (𝓞 K)) (u v : Kˣ) :
    exteriorPrincipalValuation p (u*v)=exteriorPrincipalValuation p u+exteriorPrincipalValuation p v := by
  unfold exteriorPrincipalValuation
  rw [map_mul,Units.val_mul]
  exact FractionalIdeal.count_mul K p (Units.ne_zero _) (Units.ne_zero _)

theorem exteriorPrincipalValuation_pow (p : HeightOneSpectrum (𝓞 K)) (u : Kˣ) (n : ℕ) :
    exteriorPrincipalValuation p (u^n)=(n:ℤ)*exteriorPrincipalValuation p u := by
  unfold exteriorPrincipalValuation
  rw [map_pow,Units.val_pow_eq_pow_val,FractionalIdeal.count_pow]

theorem exteriorPrincipalValuation_inv (p : HeightOneSpectrum (𝓞 K)) (u : Kˣ) :
    exteriorPrincipalValuation p u⁻¹= -exteriorPrincipalValuation p u := by
  have h := exteriorPrincipalValuation_mul p u u⁻¹
  rw [mul_inv_cancel,exteriorPrincipalValuation_one] at h
  omega

theorem exteriorPrincipalValuation_div (p : HeightOneSpectrum (𝓞 K)) (u v : Kˣ) :
    exteriorPrincipalValuation p (u/v)=exteriorPrincipalValuation p u-exteriorPrincipalValuation p v := by
  rw [div_eq_mul_inv,exteriorPrincipalValuation_mul,exteriorPrincipalValuation_inv]
  rfl

/-- The actual principal-ideal exponent as a multiplicative homomorphism
to the multiplicative copy of the additive group of integers. -/
def exteriorPrincipalValuationHom (p : HeightOneSpectrum (𝓞 K)) : Kˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (exteriorPrincipalValuation p u)
  map_one' := by
    change exteriorPrincipalValuation p 1=0
    exact exteriorPrincipalValuation_one p
  map_mul' u v := by
    change exteriorPrincipalValuation p (u*v)=exteriorPrincipalValuation p u+exteriorPrincipalValuation p v
    exact exteriorPrincipalValuation_mul p u v

/-- The genuine exterior S-units: principal ideal exponents vanish at
every height-one prime outside S. The finite set S is arbitrary. -/
def exteriorUnitSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ where
  carrier := {u | ∀ p, p ∉ S → exteriorPrincipalValuation p u=0}
  one_mem' := by intro p _; exact exteriorPrincipalValuation_one p
  mul_mem' := by
    intro u v hu hv p hp
    rw [exteriorPrincipalValuation_mul,hu p hp,hv p hp,add_zero]
  inv_mem' := by
    intro u hu p hp
    rw [exteriorPrincipalValuation_inv,hu p hp,neg_zero]

@[simp] theorem mem_exteriorUnitSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) :
    u ∈ exteriorUnitSubgroup S ↔ ∀ p, p ∉ S → exteriorPrincipalValuation p u=0 := Iff.rfl

def ExteriorSixthReduced (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) : Prop :=
  ∀ p, p ∉ S → 0 ≤ exteriorPrincipalValuation p u ∧ exteriorPrincipalValuation p u < 6

/-- A difference of two exponents in zero through five cannot be a
nonzero multiple of six. This uses the actual principal-ideal count law. -/
theorem exteriorSixthReduced_root_valuation
    (p : HeightOneSpectrum (𝓞 K)) (u v t : Kˣ)
    (hu : 0 ≤ exteriorPrincipalValuation p u ∧ exteriorPrincipalValuation p u < 6)
    (hv : 0 ≤ exteriorPrincipalValuation p v ∧ exteriorPrincipalValuation p v < 6)
    (hpow : u/v=t^6) :
    exteriorPrincipalValuation p u=exteriorPrincipalValuation p v ∧ exteriorPrincipalValuation p t=0 := by
  have h := congrArg (exteriorPrincipalValuation p) hpow
  rw [exteriorPrincipalValuation_div,exteriorPrincipalValuation_pow] at h
  constructor <;> omega

theorem exteriorSixthReduced_ratio_root
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u v t : Kˣ)
    (hu : ExteriorSixthReduced S u) (hv : ExteriorSixthReduced S v) (hpow : u/v=t^6) :
    (∀ p, p ∉ S → exteriorPrincipalValuation p u=exteriorPrincipalValuation p v) ∧
      t ∈ exteriorUnitSubgroup S := by
  constructor
  · intro p hp
    exact (exteriorSixthReduced_root_valuation p u v t (hu p hp) (hv p hp) hpow).1
  · intro p hp
    exact (exteriorSixthReduced_root_valuation p u v t (hu p hp) (hv p hp) hpow).2

theorem exteriorSixthReduced_power_iff
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u v : Kˣ)
    (hu : ExteriorSixthReduced S u) (hv : ExteriorSixthReduced S v) :
    (∃ t : Kˣ, u/v=t^6) ↔ ∃ t : exteriorUnitSubgroup S, u/v=(t:Kˣ)^6 := by
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨⟨t,(exteriorSixthReduced_ratio_root S u v t hu hv ht).2⟩,ht⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,ht⟩

/-- Multiplying a reduced row by an exterior S-unit sixth power leaves
all its exterior exponents unchanged. -/
theorem exteriorSixthReduced_mul_unit_pow
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) (hu : ExteriorSixthReduced S u)
    (t : exteriorUnitSubgroup S) : ExteriorSixthReduced S (u*(t:Kˣ)^6) := by
  intro p hp
  rw [exteriorPrincipalValuation_mul,exteriorPrincipalValuation_pow,t.2 p hp,mul_zero,add_zero]
  exact hu p hp

end
end ArtinMatthews
