module

public import ArtinMatthews.SIntegerStandardPhase
public import ArtinMatthews.ProbeStandardGaussCRTPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Literal standard e_S phases under coprime S-integer CRT. The
inverse cofactor multipliers are proved from the actual Bezout identity,
so no local phase comparison unit is set to one. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField OAI.IdealGaussCRT ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))

def sourceProductPhase (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0) :
    AddChar ((PrincipalIntegerRing S₀) ⧸ (Ideal.span {a} * Ideal.span {b})) ℂ :=
  pullAddChar (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b))
    (sIntegerQuotientPhase K (principalizingSet S₀) (a * b) (mul_ne_zero ha hb))

theorem sourceProductPhase_mk (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0)
    (x : PrincipalIntegerRing S₀) :
    sourceProductPhase S₀ a b ha hb (Ideal.Quotient.mk _ x) =
      sCharacter K (principalizingSet S₀) ((x : K) / ((a : K) * (b : K))) := by
  rw [sourceProductPhase, pullAddChar_apply, Ideal.quotEquivOfEq_mk, sIntegerQuotientPhase_mk]
  rfl

theorem sourceProductPhase_left (a b u v : PrincipalIntegerRing S₀)
    (ha : a ≠ 0) (hb : b ≠ 0) (hbez : u * a + v * b = 1) :
    leftAddChar (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)) (sourceProductPhase S₀ a b ha hb) =
      (sIntegerQuotientPhase K (principalizingSet S₀) a ha).mulShift
        (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change sourceProductPhase S₀ a b ha hb
    ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm (Ideal.Quotient.mk _ x, 0)) = _
  rw [crt_left_inverse_coordinate hbez x, sourceProductPhase_mk, AddChar.mulShift_apply,
    ← map_mul (Ideal.Quotient.mk (Ideal.span {a})) v x, sIntegerQuotientPhase_mk]
  have hbK : (b : K) ≠ 0 := fun h => hb (Subtype.ext h)
  congr 1
  change ((x : K) * (v : K) * (b : K)) / ((a : K) * (b : K)) =
    ((v : K) * (x : K)) / (a : K)
  field_simp

theorem sourceProductPhase_right (a b u v : PrincipalIntegerRing S₀)
    (ha : a ≠ 0) (hb : b ≠ 0) (hbez : u * a + v * b = 1) :
    rightAddChar (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)) (sourceProductPhase S₀ a b ha hb) =
      (sIntegerQuotientPhase K (principalizingSet S₀) b hb).mulShift
        (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change sourceProductPhase S₀ a b ha hb
    ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm (0, Ideal.Quotient.mk _ x)) = _
  rw [crt_right_inverse_coordinate hbez x, sourceProductPhase_mk, AddChar.mulShift_apply,
    ← map_mul (Ideal.Quotient.mk (Ideal.span {b})) u x, sIntegerQuotientPhase_mk]
  have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
  congr 1
  change ((x : K) * (u : K) * (a : K)) / ((a : K) * (b : K)) =
    ((u : K) * (x : K)) / (b : K)
  field_simp

end
end ArtinMatthews.SIntegerQuotient
