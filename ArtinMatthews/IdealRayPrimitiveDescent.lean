module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealCharacter
public import ArtinMatthews.VaryingKummerAnalyticRayFractionalDenominator
public import ArtinMatthews.VaryingKummerAnalyticRayFractionalDenominatorCount
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine conductor descent for a ray character at an arbitrary integral
ideal modulus. The principal-ray kernel follows from its actual principal
law and prime-to-modulus integral denominators. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace EvenIdealRayCharacter
variable {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)


theorem idealHom_principal_ray (x : Kˣ)
    (hx : IdeleGroup.principalIdele K x ∈ idelePrimeToModulusSubgroup (integralIdealRayModulus M hM)) :
    ψ.idealHom (toPrincipalIdeal (𝓞 K) K x) = 1 := by
  obtain ⟨a,b,ha,hb,hac,hbc,hab⟩ := exists_coprime_integral_fraction_of_local_units K
    (M) (hM) x
    (principal_idealRayModulus_valuation_one _ _ x hx)
  have hmul : (b:K)*(x:K)=(a:K) := by
    have hbK : (b:K) ≠ 0 := by exact_mod_cast hb
    rw [hab]
    field_simp [hbK]
  have hd := principal_idealRayModulus_integral_difference _ _ x hx a b hmul
  have he : Ideal.Quotient.mk (M) a =
      Ideal.Quotient.mk (M) b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr hd
  have hc : ψ.idealHom (integralIdealFractionalUnit (Ideal.span {a}) (by simpa using ha)) =
      ψ.idealHom (integralIdealFractionalUnit (Ideal.span {b}) (by simpa using hb)) := by
    apply Units.ext
    rw [ψ.principalLaw a ha hac,ψ.principalLaw b hb hbc,he]
  rw [toPrincipalIdeal_eq_fraction x a b ha hb hab,map_div,hc]
  simp

def rayClassCharacter : IdealRayClassGroup (integralIdealRayModulus M hM) →* ℂˣ :=
  QuotientGroup.lift (principalRayIdealSubgroup (integralIdealRayModulus M hM))
    (ψ.idealHom.comp (primeToModulusIdeals (integralIdealRayModulus M hM)).subtype) (by
      intro I hI
      obtain ⟨x,hx,he⟩ := (mem_principalRayIdealSubgroup_iff _ I).mp hI
      change ψ.idealHom (I:FractionalIdealGroup K) = 1
      rw [← he]
      exact ψ.idealHom_principal_ray hM x hx)

theorem rayClassCharacter_ideal (I : primeToModulusIdeals (integralIdealRayModulus M hM)) :
    ψ.rayClassCharacter hM (QuotientGroup.mk' (principalRayIdealSubgroup (integralIdealRayModulus M hM)) I) =
      ψ.idealHom (I:FractionalIdealGroup K) := rfl

theorem rayClassCharacter_finiteOrder :
    ∃ e : ℕ, 0 < e ∧ ∀ c, ψ.rayClassCharacter hM c ^ e = 1 := by
  obtain ⟨e,he,heq⟩ := ψ.finiteOrder
  refine ⟨e,he,fun c => ?_⟩
  obtain ⟨I,rfl⟩ := QuotientGroup.mk'_surjective _ c
  exact heq I


def conductorIdealProjection (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : M ≤ f) :
    IdealRayClassGroup (integralIdealRayModulus M hM) →*
      IdealRayClassGroup (integralIdealRayModulus f hf) :=
  idealConductorProjection (integralIdealRayModulus_antitone (hM) hf hMf)

theorem conductorIdealProjection_surjective (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : M ≤ f) :
    Function.Surjective (conductorIdealProjection hM f hf hMf) :=
  idealConductorProjection_surjective _

theorem rayClassCharacter_conductor_kernel (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : M ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (M) a) =
      if IsUnit (Ideal.Quotient.mk (M) a)
        then φ (Ideal.Quotient.mk f a) else 0) :
    (conductorIdealProjection hM f hf hMf).ker ≤ (ψ.rayClassCharacter hM).ker := by
  intro c hc
  obtain ⟨I,rfl⟩ := QuotientGroup.mk'_surjective _ c
  obtain ⟨x,hx,hIx⟩ := (idealConductorProjection_ideal_eq_one_iff
    (integralIdealRayModulus_antitone (hM) hf hMf) I).mp hc
  have hcounts : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ M →
      FractionalIdeal.count K v (spanSingleton (𝓞 K)⁰ (x:K)) = 0 := by
    intro v hv
    have H := I.property v ((integralIdealFiniteModulus_mem_support _ (hM) v).mpr hv)
    rw [← hIx,coe_toPrincipalIdeal] at H
    exact H
  obtain ⟨a,b,ha,hb,hac,hbc,hab⟩ := exists_coprime_integral_fraction_of_counts K
    (M) (hM) x hcounts
  have hmul : (b:K)*(x:K)=(a:K) := by
    have hbK : (b:K) ≠ 0 := by exact_mod_cast hb
    rw [hab]
    field_simp [hbK]
  have hd := principal_idealRayModulus_integral_difference f hf x hx a b hmul
  have he : Ideal.Quotient.mk f a = Ideal.Quotient.mk f b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr hd
  have hva := hmask a
  have hvb := hmask b
  rw [ite_eq_left ((quotient_isUnit_iff_span_coprime _ a).mpr hac)] at hva
  rw [ite_eq_left ((quotient_isUnit_iff_span_coprime _ b).mpr hbc)] at hvb
  have hval : ψ.idealHom (integralIdealFractionalUnit (Ideal.span {a}) (by simpa using ha)) =
      ψ.idealHom (integralIdealFractionalUnit (Ideal.span {b}) (by simpa using hb)) := by
    apply Units.ext
    rw [ψ.principalLaw a ha hac,ψ.principalLaw b hb hbc,hva,hvb,he]
  change ψ.idealHom (I:FractionalIdealGroup K) = 1
  rw [← hIx,toPrincipalIdeal_eq_fraction x a b ha hb hab,map_div,hval]
  simp

def descendedIdealRayCharacter (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : M ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (M) a) =
      if IsUnit (Ideal.Quotient.mk (M) a)
        then φ (Ideal.Quotient.mk f a) else 0) :
    IdealRayClassGroup (integralIdealRayModulus f hf) →* ℂˣ :=
  (QuotientGroup.lift (conductorIdealProjection hM f hf hMf).ker (ψ.rayClassCharacter hM)
    (ψ.rayClassCharacter_conductor_kernel hM f hf hMf φ hmask)).comp
      (QuotientGroup.quotientKerEquivOfSurjective (conductorIdealProjection hM f hf hMf)
        (conductorIdealProjection_surjective hM f hf hMf)).symm.toMonoidHom

theorem descendedIdealRayCharacter_projection (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : M ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (M) a) =
      if IsUnit (Ideal.Quotient.mk (M) a)
        then φ (Ideal.Quotient.mk f a) else 0)
    (c : IdealRayClassGroup (integralIdealRayModulus M hM)) :
    ψ.descendedIdealRayCharacter hM f hf hMf φ hmask (conductorIdealProjection hM f hf hMf c) =
      ψ.rayClassCharacter hM c := by
  let p := conductorIdealProjection hM f hf hMf
  let e := QuotientGroup.quotientKerEquivOfSurjective p (conductorIdealProjection_surjective hM f hf hMf)
  have he : e (QuotientGroup.mk' p.ker c) = p c := rfl
  change (QuotientGroup.lift p.ker (ψ.rayClassCharacter hM)
    (ψ.rayClassCharacter_conductor_kernel hM f hf hMf φ hmask)) (e.symm (p c)) = _
  rw [← he,MulEquiv.symm_apply_apply]
  rfl

theorem descendedIdealRayCharacter_finiteOrder (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : M ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (M) a) =
      if IsUnit (Ideal.Quotient.mk (M) a)
        then φ (Ideal.Quotient.mk f a) else 0) :
    ∃ e : ℕ, 0 < e ∧ ∀ c, ψ.descendedIdealRayCharacter hM f hf hMf φ hmask c ^ e = 1 := by
  obtain ⟨e,he,h⟩ := ψ.rayClassCharacter_finiteOrder hM
  refine ⟨e,he,fun c => ?_⟩
  obtain ⟨d,rfl⟩ := conductorIdealProjection_surjective hM f hf hMf c
  rw [ψ.descendedIdealRayCharacter_projection]
  exact h d


end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
