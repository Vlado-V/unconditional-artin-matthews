module

public import ArtinMatthews.AdicIntegerResidueEquiv
public import ArtinMatthews.SIntegerStandardPhase
public import ArtinMatthews.SIntegerSexticTransport


set_option backward.privateInPublic true
@[expose] public section

/-! The actual valuation-defined S-integer ring maps into every exterior
adic integer ring. Its residue kernel is the extended prime ideal, and
the global/local residue comparison is derived from integral coverage. -/
namespace ArtinMatthews.SIntegerAdicResidue

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open ArtinMatthews.QuadraticWeil ArtinMatthews.SIntegerPrincipalization ArtinMatthews.SIntegerQuotient
open scoped NumberField ValuativeRel Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))

local instance sIntegerResidueRelation : ValuativeRel (P.adicCompletion K) := adicRelation K P
local instance sIntegerResidueLocalField : IsNonarchimedeanLocalField (P.adicCompletion K) := adicLocalField K P

def adicIntegralOfSInteger (hP : P ∉ principalizingSet S₀) :
    PrincipalIntegerRing S₀ →+* 𝒪[P.adicCompletion K] where
  toFun x := ⟨algebraMap K (P.adicCompletion K) (x : K), (adic_mem_integer_iff K P _).mpr (by
    change Valued.v ((x : K) : P.adicCompletion K) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact x.property P hP)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ (x : K) (y : K))
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ (x : K) (y : K))

theorem adicIntegralOfSInteger_val (hP : P ∉ principalizingSet S₀) (x : PrincipalIntegerRing S₀) :
    (adicIntegralOfSInteger K S₀ P hP x : P.adicCompletion K) =
      algebraMap K (P.adicCompletion K) (x : K) := rfl

theorem adicIntegralOfSInteger_integer (hP : P ∉ principalizingSet S₀) (x : 𝓞 K) :
    adicIntegralOfSInteger K S₀ P hP (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) =
      adicIntegralOfInteger K P x := by
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply (𝓞 K) K (P.adicCompletion K) x).symm

def adicResidueOfSInteger (hP : P ∉ principalizingSet S₀) :
    PrincipalIntegerRing S₀ →+* 𝓀[P.adicCompletion K] :=
  (IsLocalRing.residue 𝒪[P.adicCompletion K]).comp (adicIntegralOfSInteger K S₀ P hP)

theorem adicResidueOfSInteger_integer (hP : P ∉ principalizingSet S₀) (x : 𝓞 K) :
    adicResidueOfSInteger K S₀ P hP (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) =
      adicResidueOfInteger K P x := by
  change IsLocalRing.residue 𝒪[P.adicCompletion K] _ = _
  rw [adicIntegralOfSInteger_integer]
  rfl

theorem adicResidueOfSInteger_eq_zero_iff (hP : P ∉ principalizingSet S₀)
    (x : PrincipalIntegerRing S₀) :
    adicResidueOfSInteger K S₀ P hP x = 0 ↔
      x ∈ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
  let C := P.adicCompletion K
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  change IsLocalRing.residue 𝒪[C] (adicIntegralOfSInteger K S₀ P hP x) = 0 ↔ _
  rw [adic_residue_eq_zero_iff]
  calc
    _ ↔ ν (algebraMap K C (x : K)) < 1 :=
      (Valuation.vlt_one_iff (ValuativeRel.valuation C)).symm.trans (Valuation.vlt_one_iff ν)
    _ ↔ P.valuation K (x : K) < 1 := by
      change Valued.v ((x : K) : P.adicCompletion K) < 1 ↔ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    _ ↔ P.valuation K (x : K) ≤ WithZero.exp (-1 : ℤ) := by
      simpa only [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero] using
        (WithZero.lt_mul_exp_iff_le (x := P.valuation K (x : K))
          (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero)
    _ ↔ _ := by
      simpa only [pow_one, Nat.cast_one] using
        (principalInteger_power_mem_iff_valuation S₀ P hP 1 x).symm

theorem adicResidueOfSInteger_ker (hP : P ∉ principalizingSet S₀) :
    RingHom.ker (adicResidueOfSInteger K S₀ P hP) =
      P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
  ext x
  exact adicResidueOfSInteger_eq_zero_iff K S₀ P hP x

theorem adicResidueOfSInteger_surjective (hP : P ∉ principalizingSet S₀) :
    Function.Surjective (adicResidueOfSInteger K S₀ P hP) := by
  intro z
  obtain ⟨r, hr⟩ := adicResidueOfInteger_surjective K P z
  refine ⟨algebraMap (𝓞 K) (PrincipalIntegerRing S₀) r, ?_⟩
  rw [adicResidueOfSInteger_integer]
  exact hr

def adicSIntegerResidueEquiv (hP : P ∉ principalizingSet S₀) :
    ((PrincipalIntegerRing S₀) ⧸ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) ≃+*
      𝓀[P.adicCompletion K] :=
  (Ideal.quotEquivOfEq (adicResidueOfSInteger_ker K S₀ P hP).symm).trans
    ((adicResidueOfSInteger K S₀ P hP).quotientKerEquivOfSurjective
      (adicResidueOfSInteger_surjective K S₀ P hP))

theorem adicSIntegerResidueEquiv_mk (hP : P ∉ principalizingSet S₀) (x : PrincipalIntegerRing S₀) :
    adicSIntegerResidueEquiv K S₀ P hP (Ideal.Quotient.mk _ x) =
      adicResidueOfSInteger K S₀ P hP x := by
  rw [adicSIntegerResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem adicIntegralOfSInteger_isUnit (hP : P ∉ principalizingSet S₀)
    (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    IsUnit (adicIntegralOfSInteger K S₀ P hP x) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  exact (adicResidueOfSInteger_eq_zero_iff K S₀ P hP x).not.mpr hx

theorem adicResidueOfSInteger_generator_compare (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (x : PrincipalIntegerRing S₀) :
    adicResidueOfSInteger K S₀ P hP x =
      adicIntegerResidueEquiv K P
        (generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ x)) := by
  obtain ⟨r, hr⟩ := principal_quotient_coverage S₀ P.asIdeal
    (by simpa only [pow_one] using principalPrimePower_coprime S₀ P hP 1) x
  have hz := (adicResidueOfSInteger_eq_zero_iff K S₀ P hP _).mpr hr
  rw [map_sub, sub_eq_zero] at hz
  have hq : Ideal.Quotient.mk (Ideal.span {a}) x =
      Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) r) := by
    apply Ideal.Quotient.eq.mpr
    rw [← ha]
    exact hr
  rw [hz, adicResidueOfSInteger_integer, hq, generatorResidueEquiv_mk, adicIntegerResidueEquiv_mk]

def adicSIntegerGeneratorResidueEquiv (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) ≃+* 𝓀[P.adicCompletion K] :=
  (Ideal.quotEquivOfEq ha.symm).trans (adicSIntegerResidueEquiv K S₀ P hP)

theorem adicSIntegerGeneratorResidueEquiv_eq (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    adicSIntegerGeneratorResidueEquiv K S₀ P hP a ha =
      (generatorResidueEquiv S₀ P hP a ha).trans (adicIntegerResidueEquiv K P) := by
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [adicSIntegerGeneratorResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    adicSIntegerResidueEquiv_mk, RingEquiv.trans_apply]
  exact adicResidueOfSInteger_generator_compare K S₀ P hP a ha x

end
end ArtinMatthews.SIntegerAdicResidue
