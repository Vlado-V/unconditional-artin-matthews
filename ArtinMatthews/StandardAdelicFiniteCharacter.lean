module

public import ArtinMatthews.StandardAdelicArchTrace
public import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient
public import Mathlib.Topology.LocallyConstant.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Construct the standard finite additive character by actual finite
strong approximation. Its value is independent of every rational
remainder choice; the kernel contains the full integral finite adeles. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def rationalCharacter : AddChar K ℂ :=
  (archCharacter K).compAddMonoidHom (algebraMap K (InfiniteAdeleRing K)).toAddMonoidHom

theorem rationalCharacter_integer (r : 𝓞 K) : rationalCharacter K (r : K) = 1 :=
  archCharacter_integer K r

theorem rationalCharacter_unitary (q : K) : ‖rationalCharacter K q‖ = 1 := archCharacter_unitary K _

def finiteRationalPart (a : ArchimedeanAdeles.Construction.FiniteAdeles K) : K :=
  (CompactQuotient.Construction.exists_rational_finite_integral_remainder K a).choose

theorem finiteRationalPart_spec (a : ArchimedeanAdeles.Construction.FiniteAdeles K) :
    a - algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) (finiteRationalPart K a) ∈
      IntegralAdeles.Construction.finiteIntegralRing K :=
  (CompactQuotient.Construction.exists_rational_finite_integral_remainder K a).choose_spec

theorem rationalCharacter_remainder_independent
    (a : ArchimedeanAdeles.Construction.FiniteAdeles K) (q r : K)
    (hq : a - algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) q ∈
      IntegralAdeles.Construction.finiteIntegralRing K)
    (hr : a - algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) r ∈
      IntegralAdeles.Construction.finiteIntegralRing K) :
    rationalCharacter K q = rationalCharacter K r := by
  have hdiff : algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) (q - r) ∈
      IntegralAdeles.Construction.finiteIntegralRing K := by
    have h := (IntegralAdeles.Construction.finiteIntegralRing K).sub_mem hr hq
    convert h using 1
    rw [map_sub]
    abel
  obtain ⟨c, hc⟩ := (IntegralAdeles.Construction.rational_mem_finiteIntegral_iff K (q-r)).mp hdiff
  have hphase : rationalCharacter K (q-r) = 1 := by rw [← hc]; exact rationalCharacter_integer K c
  rw [AddChar.map_sub_eq_div] at hphase
  exact (div_eq_one_iff_eq (AddChar.val_isUnit (rationalCharacter K) r).ne_zero).mp hphase

def finitePhase (a : ArchimedeanAdeles.Construction.FiniteAdeles K) : ℂ :=
  (rationalCharacter K (finiteRationalPart K a))⁻¹

theorem finitePhase_eq (a : ArchimedeanAdeles.Construction.FiniteAdeles K) (q : K)
    (hq : a - algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) q ∈
      IntegralAdeles.Construction.finiteIntegralRing K) :
    finitePhase K a = (rationalCharacter K q)⁻¹ := by
  exact congrArg Inv.inv (rationalCharacter_remainder_independent K a _ q (finiteRationalPart_spec K a) hq)

theorem finitePhase_integral (a : ArchimedeanAdeles.Construction.FiniteAdeles K)
    (ha : a ∈ IntegralAdeles.Construction.finiteIntegralRing K) : finitePhase K a = 1 := by
  have h := finitePhase_eq K a 0 (by simpa only [map_zero, sub_zero] using ha)
  simpa only [AddChar.map_zero_eq_one, inv_one] using h

def finiteCharacter : AddChar (ArchimedeanAdeles.Construction.FiniteAdeles K) ℂ where
  toFun := finitePhase K
  map_zero_eq_one' := finitePhase_integral K 0 (zero_mem _)
  map_add_eq_mul' a b := by
    have hsum : a+b - algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K)
        (finiteRationalPart K a + finiteRationalPart K b) ∈ IntegralAdeles.Construction.finiteIntegralRing K := by
      have h := (IntegralAdeles.Construction.finiteIntegralRing K).add_mem
        (finiteRationalPart_spec K a) (finiteRationalPart_spec K b)
      convert h using 1
      rw [map_add]
      abel
    rw [finitePhase_eq K (a+b) _ hsum, AddChar.map_add_eq_mul, mul_inv]
    rfl

theorem finiteCharacter_eq (a : ArchimedeanAdeles.Construction.FiniteAdeles K) (q : K)
    (hq : a - algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) q ∈
      IntegralAdeles.Construction.finiteIntegralRing K) :
    finiteCharacter K a = (rationalCharacter K q)⁻¹ := finitePhase_eq K a q hq

theorem finiteCharacter_integral (a : ArchimedeanAdeles.Construction.FiniteAdeles K)
    (ha : a ∈ IntegralAdeles.Construction.finiteIntegralRing K) : finiteCharacter K a = 1 := finitePhase_integral K a ha

theorem finiteCharacter_rational (q : K) :
    finiteCharacter K (algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) q) =
      (rationalCharacter K q)⁻¹ :=
  finiteCharacter_eq K _ q (by rw [sub_self]; exact zero_mem _)

theorem finiteCharacter_unitary (a : ArchimedeanAdeles.Construction.FiniteAdeles K) :
    ‖finiteCharacter K a‖ = 1 := by
  change ‖(rationalCharacter K _)⁻¹‖ = 1
  rw [norm_inv, rationalCharacter_unitary, inv_one]

theorem finiteCharacter_locallyConstant : IsLocallyConstant (finiteCharacter K) := by
  apply (IsLocallyConstant.iff_exists_open (finiteCharacter K)).mpr
  intro a
  let U : Set (ArchimedeanAdeles.Construction.FiniteAdeles K) :=
    {b | b-a ∈ IntegralAdeles.Construction.finiteIntegralRing K}
  refine ⟨U, (IntegralAdeles.Construction.isOpen_finiteIntegralRing K).preimage
    (continuous_id.sub continuous_const), ?_, ?_⟩
  · change a-a ∈ IntegralAdeles.Construction.finiteIntegralRing K
    rw [sub_self]
    exact zero_mem _
  · intro b hb
    have h := finiteCharacter_integral K (b-a) hb
    rw [AddChar.map_sub_eq_div] at h
    exact (div_eq_one_iff_eq (AddChar.val_isUnit (finiteCharacter K) a).ne_zero).mp h

theorem finiteCharacter_continuous : Continuous (finiteCharacter K) :=
  (finiteCharacter_locallyConstant K).continuous

end
end ArtinMatthews.StandardAdelic
