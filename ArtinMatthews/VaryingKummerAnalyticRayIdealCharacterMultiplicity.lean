module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealSeries
public import ArtinMatthews.VaryingKummerAnalyticRayIdealCoefficients
public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedAlgebra
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Actual residue-fiber multiplicity at a genuine ideal conductor. Equal
residues differ by an ordinary class-group character on coprime ideals.
The bound counts distinct Hecke coefficient functions, not arbitrary values
of an extension at the omitted bad primes. -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}

def classIdeal (hM : M ≠ ⊥) (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  coprimeClassRepresentative M hM c

theorem classIdeal_ne_bot (hM : M ≠ ⊥) (c : ClassGroup (𝓞 K)) :
    (classIdeal hM c).val ≠ ⊥ :=
  mem_nonZeroDivisors_iff_ne_zero.mp (classIdeal hM c).property

theorem classIdeal_coprime (hM : M ≠ ⊥) (c : ClassGroup (𝓞 K)) :
    IsCoprime (classIdeal hM c).val M :=
  (coprimeClassRepresentative_spec M hM c).1

theorem classIdeal_class (hM : M ≠ ⊥) (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (integralIdealFractionalUnit (classIdeal hM c).val
      (classIdeal_ne_bot hM c)) = c := by
  change ClassGroup.mk K (FractionalIdeal.mk0 K (classIdeal hM c)) = c
  rw [ClassGroup.mk_mk0]
  exact (coprimeClassRepresentative_spec M hM c).2

variable (ψ : EvenIdealRayCharacter K M)

theorem coprime_inverse_product (hψ : ψ.residue = 1)
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIc : IsCoprime I M) (hJc : IsCoprime J M)
    (hclass : ClassGroup.mk K (integralIdealFractionalUnit J hJ) =
      (ClassGroup.mk K (integralIdealFractionalUnit I hI))⁻¹) :
    ψ.idealHom (integralIdealFractionalUnit I hI) *
      ψ.idealHom (integralIdealFractionalUnit J hJ) = 1 := by
  let Jf : integralIdealClassFiber (integralIdealFractionalUnit I hI) :=
    ⟨integralIdealFractionalUnit J hJ,FractionalIdeal.coeIdeal_le_one,hclass⟩
  let a := idealIntegerElement I hI (idealElementRepresentative _ Jf)
  have ha : a ≠ 0 := EvenRayCharacter.generator_integer_ne_zero I hI Jf
  have hp : Ideal.span {a} = I * J := by
    have H := EvenRayCharacter.generator_principal_product I hI Jf
    change Ideal.span {a} = I * EvenRayCharacter.underlyingIdeal
      ⟨integralIdealFractionalUnit J hJ,FractionalIdeal.coeIdeal_le_one⟩ at H
    simpa only [EvenRayCharacter.underlyingIdeal_integralUnit] using H
  have hac : IsCoprime (Ideal.span {a}) M := by
    rw [hp]
    exact IsCoprime.mul_left_iff.mpr ⟨hIc,hJc⟩
  have H := ψ.principalLaw a ha hac
  rw [hψ,MulChar.one_apply ((quotient_isUnit_iff_span_coprime _ a).mpr hac)] at H
  have HG := EvenRayCharacter.generator_fractional_product I hI Jf
  change integralIdealFractionalUnit (Ideal.span {a}) _ =
    integralIdealFractionalUnit I hI * integralIdealFractionalUnit J hJ at HG
  rw [HG,map_mul,Units.val_mul] at H
  exact Units.ext H

variable (hM : M ≠ ⊥)
include hM

theorem idealHom_eq_of_coprime_class (hψ : ψ.residue = 1)
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIc : IsCoprime I M) (hJc : IsCoprime J M)
    (hclass : ClassGroup.mk K (integralIdealFractionalUnit I hI) =
      ClassGroup.mk K (integralIdealFractionalUnit J hJ)) :
    ψ.idealHom (integralIdealFractionalUnit I hI) =
      ψ.idealHom (integralIdealFractionalUnit J hJ) := by
  let c := ClassGroup.mk K (integralIdealFractionalUnit I hI)
  let L := (classIdeal hM c⁻¹).val
  have hL : L ≠ ⊥ := classIdeal_ne_bot hM c⁻¹
  have hcL : IsCoprime L M := classIdeal_coprime hM c⁻¹
  have hlclass : ClassGroup.mk K (integralIdealFractionalUnit L hL) = c⁻¹ :=
    classIdeal_class hM c⁻¹
  have HI := ψ.coprime_inverse_product hψ L I hL hI hcL hIc (by rw [hlclass,inv_inv])
  have HJ := ψ.coprime_inverse_product hψ L J hL hJ hcL hJc (by
    rw [hlclass,inv_inv]
    exact hclass.symm)
  exact mul_left_cancel (HI.trans HJ.symm)

def classValue (c : ClassGroup (𝓞 K)) : ℂˣ :=
  ψ.idealHom (integralIdealFractionalUnit (classIdeal hM c).val (classIdeal_ne_bot hM c))

theorem idealHom_eq_classValue (hψ : ψ.residue = 1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hc : IsCoprime I M) :
    ψ.idealHom (integralIdealFractionalUnit I hI) =
      ψ.classValue hM (ClassGroup.mk K (integralIdealFractionalUnit I hI)) := by
  apply ψ.idealHom_eq_of_coprime_class hM hψ I _ hI _ hc (classIdeal_coprime hM _)
  exact (classIdeal_class hM _).symm

theorem classValue_one (hψ : ψ.residue = 1) : ψ.classValue hM 1 = 1 := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 K)) M := by
    rw [← Ideal.one_eq_top]
    exact isCoprime_one_left
  have H := ψ.idealHom_eq_classValue hM hψ ⊤ top_ne_bot hc
  simpa only [integralIdealFractionalUnit_top,map_one] using H.symm

theorem classValue_mul (hψ : ψ.residue = 1) (c e : ClassGroup (𝓞 K)) :
    ψ.classValue hM (c*e) = ψ.classValue hM c * ψ.classValue hM e := by
  let I := (classIdeal hM c).val
  let J := (classIdeal hM e).val
  have hI : I ≠ ⊥ := classIdeal_ne_bot hM c
  have hJ : J ≠ ⊥ := classIdeal_ne_bot hM e
  have hc : IsCoprime (I*J) M :=
    IsCoprime.mul_left_iff.mpr ⟨classIdeal_coprime hM c,classIdeal_coprime hM e⟩
  have H := ψ.idealHom_eq_classValue hM hψ (I*J) (mul_ne_zero hI hJ) hc
  rw [EvenRayCharacter.integralUnit_mul I J hI hJ,map_mul,map_mul] at H
  have HI : ClassGroup.mk K (integralIdealFractionalUnit I hI) = c := classIdeal_class hM c
  have HJ : ClassGroup.mk K (integralIdealFractionalUnit J hJ) = e := classIdeal_class hM e
  rw [HI,HJ] at H
  exact H.symm

def classCharacter (hψ : ψ.residue = 1) : ClassGroup (𝓞 K) →* ℂ where
  toFun c := (ψ.classValue hM c : ℂ)
  map_one' := by rw [ψ.classValue_one hM hψ]; rfl
  map_mul' c e := by rw [ψ.classValue_mul hM hψ]; rfl

omit hM in
def sameResidueQuotient (φ : EvenIdealRayCharacter K M) (hres : ψ.residue = φ.residue) :
    EvenIdealRayCharacter K M where
  idealHom := ψ.idealHom / φ.idealHom
  finiteOrder := by
    obtain ⟨e,he,hψ⟩ := ψ.finiteOrder
    obtain ⟨f,hf,hφ⟩ := φ.finiteOrder
    refine ⟨e*f,Nat.mul_pos he hf,fun J => ?_⟩
    have hp : ψ.idealHom J ^ (e*f) = 1 := by rw [pow_mul,hψ,one_pow]
    have hq : φ.idealHom J ^ (e*f) = 1 := by rw [Nat.mul_comm e f,pow_mul,hφ,one_pow]
    simp only [MonoidHom.div_apply,div_pow,hp,hq,one_div_one]
  residue := 1
  principalLaw a ha hc := by
    have hn : φ.residue (Ideal.Quotient.mk M a) ≠ 0 := by
      rw [← φ.principalLaw a ha hc]
      exact Units.ne_zero _
    rw [MulChar.one_apply ((quotient_isUnit_iff_span_coprime _ a).mpr hc)]
    change ((ψ.idealHom _ / φ.idealHom _ : ℂˣ) : ℂ) = 1
    rw [Units.val_div_eq_div_val,ψ.principalLaw a ha hc,φ.principalLaw a ha hc,hres]
    exact div_self hn

omit hM in
def AgreesOnCoprimeIdeals (φ : EvenIdealRayCharacter K M) : Prop :=
  ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥), IsCoprime I M →
    ψ.idealHom (integralIdealFractionalUnit I hI) = φ.idealHom (integralIdealFractionalUnit I hI)

def sameResidueClassCharacter (φ : EvenIdealRayCharacter K M) (hres : ψ.residue = φ.residue) :
    ClassGroup (𝓞 K) →* ℂ :=
  (ψ.sameResidueQuotient φ hres).classCharacter hM rfl

theorem sameResidueClassCharacter_ideal (φ : EvenIdealRayCharacter K M)
    (hres : ψ.residue = φ.residue) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hc : IsCoprime I M) :
    ψ.sameResidueClassCharacter hM φ hres (ClassGroup.mk K (integralIdealFractionalUnit I hI)) =
      (ψ.idealHom (integralIdealFractionalUnit I hI):ℂ) /
        (φ.idealHom (integralIdealFractionalUnit I hI):ℂ) := by
  have H := (ψ.sameResidueQuotient φ hres).idealHom_eq_classValue hM rfl I hI hc
  change ((ψ.sameResidueQuotient φ hres).classValue hM
    (ClassGroup.mk K (integralIdealFractionalUnit I hI)) : ℂ) = _
  simpa only [sameResidueQuotient,MonoidHom.div_apply,Units.val_div_eq_div_val] using
    (congrArg (fun z : ℂˣ => (z:ℂ)) H).symm

theorem sameResidueClassCharacter_eq_iff_agrees (φ τ : EvenIdealRayCharacter K M)
    (hψ : ψ.residue = τ.residue) (hφ : φ.residue = τ.residue) :
    ψ.sameResidueClassCharacter hM τ hψ = φ.sameResidueClassCharacter hM τ hφ ↔
      ψ.AgreesOnCoprimeIdeals φ := by
  constructor
  · intro h I hI hc
    have H := congrArg (fun χ : ClassGroup (𝓞 K) →* ℂ =>
      χ (ClassGroup.mk K (integralIdealFractionalUnit I hI))) h
    rw [sameResidueClassCharacter_ideal ψ hM τ hψ I hI hc,
      sameResidueClassCharacter_ideal φ hM τ hφ I hI hc] at H
    apply Units.ext
    exact (div_left_inj' (Units.ne_zero (τ.idealHom _))).mp H
  · intro h
    ext c
    rw [← classIdeal_class hM c]
    rw [sameResidueClassCharacter_ideal ψ hM τ hψ _ (classIdeal_ne_bot hM c) (classIdeal_coprime hM c),
      sameResidueClassCharacter_ideal φ hM τ hφ _ (classIdeal_ne_bot hM c) (classIdeal_coprime hM c)]
    rw [h _ (classIdeal_ne_bot hM c) (classIdeal_coprime hM c)]

omit hM in
theorem agreesOnCoprimeIdeals_iff_coefficient_eq (φ : EvenIdealRayCharacter K M) :
    ψ.AgreesOnCoprimeIdeals φ ↔ ψ.coefficient = φ.coefficient := by
  constructor
  · intro h
    ext J
    unfold coefficient
    by_cases hc : IsCoprime (EvenRayCharacter.underlyingIdeal J) M
    · rw [ite_eq_left hc,ite_eq_left hc]
      have H := h (EvenRayCharacter.underlyingIdeal J) (EvenRayCharacter.underlyingIdeal_ne_bot J) hc
      rw [EvenRayCharacter.underlyingIdeal_unit] at H
      exact congrArg (fun z : ℂˣ => (z:ℂ)) H
    · rw [ite_eq_right hc,ite_eq_right hc]
  · intro h I hI hc
    have H := congrFun h
      (⟨integralIdealFractionalUnit I hI,FractionalIdeal.coeIdeal_le_one⟩ : integralFractionalIdeals K)
    simp only [coefficient,EvenRayCharacter.underlyingIdeal_integralUnit,ite_eq_left hc] at H
    exact Units.ext H

omit ψ hM in
def CoprimeSeparatedOn {ι : Type*} (F : ι → EvenIdealRayCharacter K M) (A : Finset ι) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, (F i).AgreesOnCoprimeIdeals (F j) → i = j

omit ψ hM in
theorem coprimeSeparatedOn_of_coefficient_injective {ι : Type*}
    (F : ι → EvenIdealRayCharacter K M) (A : Finset ι)
    (hF : Set.InjOn (fun i => (F i).coefficient) A) : CoprimeSeparatedOn F A := by
  intro i hi j hj h
  exact hF hi hj ((agreesOnCoprimeIdeals_iff_coefficient_eq _ _).mp h)

omit ψ in
theorem residue_fiber_card_le_classNumber {ι : Type*}
    (F : ι → EvenIdealRayCharacter K M) (A : Finset ι) (hF : CoprimeSeparatedOn F A)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) :
    (A.filter fun i => (F i).residue = χ).card ≤ NumberField.classNumber K := by
  classical
  let B := A.filter fun i => (F i).residue = χ
  change B.card ≤ _
  by_cases hB : B.Nonempty
  · obtain ⟨i₀,hi₀⟩ := hB
    have hr (i : {i // i ∈ B}) : (F i.val).residue = (F i₀).residue :=
      (Finset.mem_filter.mp i.property).2.trans (Finset.mem_filter.mp hi₀).2.symm
    let C : {i // i ∈ B} → (ClassGroup (𝓞 K) →* ℂ) :=
      fun i => (F i.val).sameResidueClassCharacter hM (F i₀) (hr i)
    have hC : Function.Injective C := by
      intro i j hij
      apply Subtype.ext
      apply hF i.val (Finset.mem_filter.mp i.property).1 j.val (Finset.mem_filter.mp j.property).1
      exact ((F i.val).sameResidueClassCharacter_eq_iff_agrees hM (F j.val) (F i₀)
        (hr i) (hr j)).mp hij
    have hlin := (linearIndependent_monoidHom (ClassGroup (𝓞 K)) ℂ).comp C hC
    have hc := hlin.fintype_card_le_finrank
    simpa only [Fintype.card_coe,Module.finrank_fintype_fun_eq_card,NumberField.classNumber] using hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hB]
    exact Nat.zero_le _

end
end ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
