module

public import ArtinMatthews.VaryingKummerAnalyticMixedCovolume
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.RingTheory.ClassGroup.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact general-field ideal/unit orbit decomposition extracted from OpenAI
PrimePackets/ZetaResidues.lean. These source arguments require neither totally
real signature nor odd degree. The relative ideal definition is from
PrimePackets/PacketAlgebra.lean. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal MeasureTheory
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section

def relativeElementIdeal {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  toPrincipalIdeal (𝓞 K) K a * I⁻¹

theorem fractionalIdeal_same_class {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.mk K I = ClassGroup.mk K J ↔
      ∃ x : K, x ≠ 0 ∧ FractionalIdeal.spanSingleton R⁰ x * (I : FractionalIdeal R⁰ K) = J := by
  refine (ClassGroup.equiv K).injective.eq_iff.symm.trans ?_
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.refl_apply,
    QuotientGroup.mk'_eq_mk', mem_principal_ideals_iff, Units.ext_iff, Units.val_mul,
    Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.refl_apply]
  constructor
  · rintro ⟨X, ⟨x, hX⟩, hx⟩
    refine ⟨x, ?_, ?_⟩
    · rintro rfl
      simp [X.ne_zero.symm] at hX
    · simpa only [hX, mul_comm] using hx
  · rintro ⟨x, hx, heq⟩
    refine ⟨toPrincipalIdeal R K (Units.mk0 x hx), ⟨x, by simp⟩, ?_⟩
    simpa only [coe_toPrincipalIdeal, Units.val_mk0, mul_comm] using heq

lemma relativeElementIdeal_le_one_iff {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    (relativeElementIdeal I a : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 ↔
      (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  constructor
  · intro h
    simp only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal] at h
    have H := mul_le_mul_right h (I : FractionalIdeal (𝓞 K)⁰ K)
    rw [mul_comm (I : FractionalIdeal (𝓞 K)⁰ K) (_ * _),mul_assoc,
      Units.inv_mul,mul_one,mul_one] at H
    exact H
  · intro h
    have H := mul_le_mul_right h (↑(I⁻¹) : FractionalIdeal (𝓞 K)⁰ K)
    simpa only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal,Units.mul_inv,Units.inv_mul,mul_comm,mul_left_comm,mul_assoc] using H

lemma relativeElementIdeal_class {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    ClassGroup.mk K (relativeElementIdeal I a) = (ClassGroup.mk K I)⁻¹ := by
  have hp : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K a) = 1 := by
    exact ClassGroup.mk_eq_one_iff.mpr (by
      rw [coe_toPrincipalIdeal,FractionalIdeal.coe_spanSingleton]
      exact ⟨⟨(a : K),rfl⟩⟩)
  simp only [relativeElementIdeal,map_mul,hp,map_inv,one_mul]

lemma relativeElementIdeal_eq_iff {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : Kˣ) :
    relativeElementIdeal I a = relativeElementIdeal I b ↔
      ∃ z : (𝓞 K)ˣ, z • (a : K) = (b : K) := by
  rw [relativeElementIdeal,relativeElementIdeal,mul_right_cancel_iff,Units.ext_iff,
    coe_toPrincipalIdeal,coe_toPrincipalIdeal,FractionalIdeal.spanSingleton_eq_spanSingleton]

 

def integralIdealClassFiber {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ //
    (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 ∧ ClassGroup.mk K J = (ClassGroup.mk K I)⁻¹}

 

def nonzeroIdealElements {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}

def relativeElementClassMap {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : nonzeroIdealElements I) : integralIdealClassFiber I :=
  ⟨relativeElementIdeal I a.val,(relativeElementIdeal_le_one_iff I a.val).mpr a.property,
    relativeElementIdeal_class I a.val⟩

theorem relativeElementClassMap_surjective {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Surjective (relativeElementClassMap I) := by
  intro J
  have hclass : ClassGroup.mk K I⁻¹ = ClassGroup.mk K J.val := by rw [map_inv,J.property.2]
  obtain ⟨a,ha,h⟩ := (fractionalIdeal_same_class I⁻¹ J.val).mp hclass
  have he : relativeElementIdeal I (Units.mk0 a ha) = J.val := by
    apply Units.ext
    simpa only [relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal,Units.val_mk0] using h
  refine ⟨⟨Units.mk0 a ha,?_⟩,Subtype.ext he⟩
  apply (relativeElementIdeal_le_one_iff I _).mp
  rw [he]
  exact J.property.1

 

def idealElementRepresentative {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (J : integralIdealClassFiber I) : nonzeroIdealElements I :=
  (relativeElementClassMap_surjective I J).choose

lemma idealElementRepresentative_spec {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (J : integralIdealClassFiber I) :
    relativeElementClassMap I (idealElementRepresentative I J) = J :=
  (relativeElementClassMap_surjective I J).choose_spec

 

def idealElementUnitAction {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : (𝓞 K)ˣ) (a : nonzeroIdealElements I) :
    nonzeroIdealElements I :=
  ⟨Units.map (algebraMap (𝓞 K) K).toMonoidHom z * a.val,
    show z • (a.val : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K) from
      (I : Submodule (𝓞 K) K).smul_mem (z : 𝓞 K) a.property⟩

lemma relativeElementClassMap_unitAction {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : (𝓞 K)ˣ) (a : nonzeroIdealElements I) :
    relativeElementClassMap I (idealElementUnitAction I z a) = relativeElementClassMap I a := by
  apply Subtype.ext
  apply ((relativeElementIdeal_eq_iff I a.val _).mpr ⟨z,rfl⟩).symm

lemma idealElementUnitAction_injective {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : nonzeroIdealElements I) :
    Function.Injective (fun z : (𝓞 K)ˣ => idealElementUnitAction I z a) := by
  intro z w h
  have he := congrArg (fun b : nonzeroIdealElements I => b.val) h
  change Units.map (algebraMap (𝓞 K) K).toMonoidHom z * a.val =
    Units.map (algebraMap (𝓞 K) K).toMonoidHom w * a.val at he
  have hh := congrArg (fun b : Kˣ => (b : K)) (mul_right_cancel he)
  apply Units.ext
  exact (IsFractionRing.injective (𝓞 K) K) hh

 

theorem exists_unique_unit_of_relativeElementClassMap_eq
    {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : nonzeroIdealElements I)
    (h : relativeElementClassMap I a = relativeElementClassMap I b) :
    ∃! z : (𝓞 K)ˣ, idealElementUnitAction I z a = b := by
  obtain ⟨z,hz⟩ := (relativeElementIdeal_eq_iff I a.val b.val).mp
    (congrArg Subtype.val h)
  refine ⟨z,?_,?_⟩
  · apply Subtype.ext
    apply Units.ext
    exact hz
  · intro w hw
    apply idealElementUnitAction_injective I a
    exact hw.trans (by apply Subtype.ext; apply Units.ext; exact hz.symm)

def idealElementDecompositionMap {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Σ _J : integralIdealClassFiber I, (𝓞 K)ˣ) → nonzeroIdealElements I :=
  fun x => idealElementUnitAction I x.2 (idealElementRepresentative I x.1)

 

def idealElementDecomposition {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Σ _J : integralIdealClassFiber I, (𝓞 K)ˣ) ≃ nonzeroIdealElements I :=
  Equiv.ofBijective (idealElementDecompositionMap I) (by
    constructor
    · rintro ⟨J,z⟩ ⟨L,w⟩ h
      have he := congrArg (relativeElementClassMap I) h
      simp only [idealElementDecompositionMap,relativeElementClassMap_unitAction,
        idealElementRepresentative_spec] at he
      subst L
      have hz : z = w := idealElementUnitAction_injective I _ h
      subst w
      rfl
    · intro a
      let J := relativeElementClassMap I a
      obtain ⟨z,hz,_⟩ := exists_unique_unit_of_relativeElementClassMap_eq I
        (idealElementRepresentative I J) a (idealElementRepresentative_spec I J)
      exact ⟨⟨J,z⟩,hz⟩)

 

def nonzeroIdealElementEquiv {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    {a : (I : Submodule (𝓞 K) K).restrictScalars ℤ // (a : K) ≠ 0} ≃
      nonzeroIdealElements I where
  toFun a := ⟨Units.mk0 a.1.1 a.2,a.1.2⟩
  invFun a := ⟨⟨a.1,a.2⟩,a.1.ne_zero⟩
  left_inv _ := rfl
  right_inv a := by apply Subtype.ext; apply Units.ext; rfl

lemma tsum_relativeElementIdeal {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (W : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℝ≥0∞) (F : K → ℝ≥0∞) :
    (∑' a : nonzeroIdealElements I, W (relativeElementIdeal I a.1) * F a.1.1) =
      ∑' J : integralIdealClassFiber I, W J.1 *
        ∑' z : (𝓞 K)ˣ, F ((z : K)*(idealElementRepresentative I J).1.1) := by
  rw [← (idealElementDecomposition I).tsum_eq,ENNReal.tsum_sigma']
  apply tsum_congr
  intro J
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  have h := congrArg Subtype.val ((relativeElementClassMap_unitAction I z
    (idealElementRepresentative I J)).trans (idealElementRepresentative_spec I J))
  change W (relativeElementIdeal I (idealElementUnitAction I z (idealElementRepresentative I J)).1) *
    F ((z : K)*(idealElementRepresentative I J).1.1) = _
  rw [show relativeElementIdeal I (idealElementUnitAction I z (idealElementRepresentative I J)).1 = J.1 from h]

end
end ArtinMatthews.VaryingKummerAnalytic
