module

public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive integer rows are genuine reduced residue classes and integer translates. -/
noncomputable section
open Set
namespace ArtinMatthews

abbrev EisensteinCoprimeResidues (c : ℕ) := {a : Fin c // Nat.Coprime c a.val}

theorem eisensteinCoprimeResidues_card (c : ℕ) :
    Fintype.card (EisensteinCoprimeResidues c) = c.totient := by
  let e : EisensteinCoprimeResidues c ≃ {m : ℕ // m<c ∧ Nat.Coprime c m} :=
    { toFun := fun a => ⟨a.val.val,a.val.isLt,a.property⟩
      invFun := fun a => ⟨⟨a.val,a.property.1⟩,a.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_eq_fintype_card,Nat.card_congr e]
  exact (Nat.totient_eq_card_lt_and_coprime c).symm

def eisensteinResidueTranslate (c : ℕ) (v : EisensteinCoprimeResidues c × ℤ) :
    {d : ℤ // IsCoprime (c:ℤ) d} :=
  ⟨(v.1.val.val:ℤ)+(c:ℤ)*v.2,by
    have h : IsCoprime (c:ℤ) (v.1.val.val:ℤ) := by
      simpa only [Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast] using v.1.property
    exact h.add_mul_left_right v.2⟩

theorem eisensteinResidueTranslate_bijective (c : ℕ) (hc : 0<c) :
    Function.Bijective (eisensteinResidueTranslate c) := by
  have hcZ : 0<(c:ℤ) := by exact_mod_cast hc
  constructor
  · rintro ⟨a,k⟩ ⟨b,l⟩ h
    have he := congrArg Subtype.val h
    change (a.val.val:ℤ)+(c:ℤ)*k = (b.val.val:ℤ)+(c:ℤ)*l at he
    have hmod := congrArg (fun d : ℤ => d%(c:ℤ)) he
    have ha : 0≤(a.val.val:ℤ) ∧ (a.val.val:ℤ)<c := ⟨by positivity,by exact_mod_cast a.val.isLt⟩
    have hb : 0≤(b.val.val:ℤ) ∧ (b.val.val:ℤ)<c := ⟨by positivity,by exact_mod_cast b.val.isLt⟩
    simp only [Int.add_mul_emod_self_left,Int.emod_eq_of_lt ha.1 ha.2,
      Int.emod_eq_of_lt hb.1 hb.2] at hmod
    have hab : a=b := by
      apply Subtype.ext
      apply Fin.ext
      exact_mod_cast hmod
    subst b
    have hkl : k=l := mul_left_cancel₀ hcZ.ne' (add_left_cancel he)
    subst l
    rfl
  · intro d
    let r := d.val%(c:ℤ)
    have hr0 : 0≤r := Int.emod_nonneg _ hcZ.ne'
    have hrc : r<(c:ℤ) := Int.emod_lt_of_pos _ hcZ
    have hr : IsCoprime (c:ℤ) r := by
      have hd : IsCoprime (c:ℤ) (r+(c:ℤ)*(d.val/(c:ℤ))) := by
        simpa only [r,Int.emod_add_mul_ediv] using d.property
      exact hd.of_add_mul_left_right
    let a : EisensteinCoprimeResidues c :=
      ⟨⟨r.toNat,by omega⟩,by
        have hcast : (r.toNat:ℤ)=r := Int.toNat_of_nonneg hr0
        have ha : IsCoprime (c:ℤ) (r.toNat:ℤ) := hcast ▸ hr
        simpa only [Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast] using ha⟩
    refine ⟨(a,d.val/(c:ℤ)),?_⟩
    apply Subtype.ext
    change (r.toNat:ℤ)+(c:ℤ)*(d.val/(c:ℤ))=d.val
    rw [Int.toNat_of_nonneg hr0]
    exact Int.emod_add_mul_ediv _ _

def eisensteinResidueTranslateEquiv (c : ℕ) (hc : 0<c) :
    EisensteinCoprimeResidues c × ℤ ≃ {d : ℤ // IsCoprime (c:ℤ) d} :=
  Equiv.ofBijective _ (eisensteinResidueTranslate_bijective c hc)

theorem eisensteinResidueTranslateEquiv_apply (c : ℕ) (hc : 0<c)
    (a : EisensteinCoprimeResidues c) (k : ℤ) :
    (eisensteinResidueTranslateEquiv c hc (a,k)).val = (a.val.val:ℤ)+(c:ℤ)*k := rfl

end ArtinMatthews
