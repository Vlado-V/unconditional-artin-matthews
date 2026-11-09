module

public import ArtinMatthews.SpectralTrueWidthDoubleCosets


set_option backward.privateInPublic true
@[expose] public section

/-! The common-period finite residue model is an explicit rectangular
refinement of the genuine least-width double-coset model. -/

noncomputable section
open Matrix
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

theorem integer_interval_translate_bound {L Q x a : ℤ} (hL : 0 < L)
    (hx : 0 ≤ x ∧ x < L) (ha : 0 ≤ a ∧ a < Q) :
    0 ≤ x + L*a ∧ x + L*a < L*Q := by
  have hLa : 0 ≤ L*a := mul_nonneg hL.le ha.1
  have hQa : 0 ≤ L*(Q-a-1) := mul_nonneg hL.le (by omega)
  constructor <;> nlinarith

theorem gamma0CuspFrequencyStep_pos (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    0 < gamma0CuspFrequencyStep N r := by
  have h := gamma0CuspFrequencyStep_mul_width N r
  have hN := NeZero.pos N
  nlinarith

def gamma0CuspWidthRefinement (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ)
    (p : gamma0TrueWidthReducedMatrix N r s c ×
      Fin (gamma0CuspFrequencyStep N s) × Fin (gamma0CuspFrequencyStep N r)) :
    gamma0CuspReducedMatrix N r s c := by
  let R := integerTranslation ((gamma0CuspTrueWidth N s : ℤ) * p.2.1.val) * p.1.val *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ) * p.2.2.val)
  refine ⟨R,gamma0CuspCorrespondence_trueWidth_translate N r s p.1.val
    p.1.property.1 p.2.1.val p.2.2.val,
    (integerTranslation_entries _ _ p.1.val).2.1.trans p.1.property.2.1,?_⟩
  have hs : (gamma0CuspTrueWidth N s : ℤ) * gamma0CuspFrequencyStep N s = N := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N s
  have hr : (gamma0CuspTrueWidth N r : ℤ) * gamma0CuspFrequencyStep N r = N := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hA := integer_interval_translate_bound
    (L := (gamma0CuspTrueWidth N s : ℤ) * c)
    (Q := (gamma0CuspFrequencyStep N s : ℤ))
    (x := p.1.val 0 0) (a := p.2.1.val)
    (lt_of_le_of_lt p.1.property.2.2.1 p.1.property.2.2.2.1)
    ⟨p.1.property.2.2.1,p.1.property.2.2.2.1⟩
    ⟨by positivity,by exact_mod_cast p.2.1.isLt⟩
  have hD := integer_interval_translate_bound
    (L := (gamma0CuspTrueWidth N r : ℤ) * c)
    (Q := (gamma0CuspFrequencyStep N r : ℤ))
    (x := p.1.val 1 1) (a := p.2.2.val)
    (lt_of_le_of_lt p.1.property.2.2.2.2.1 p.1.property.2.2.2.2.2)
    ⟨p.1.property.2.2.2.2.1,p.1.property.2.2.2.2.2⟩
    ⟨by positivity,by exact_mod_cast p.2.2.isLt⟩
  obtain ⟨hRA,_,hRD⟩ := integerTranslation_entries
    ((gamma0CuspTrueWidth N s : ℤ) * p.2.1.val)
    ((gamma0CuspTrueWidth N r : ℤ) * p.2.2.val) p.1.val
  change 0 ≤ R 0 0 ∧ R 0 0 < (N : ℤ)*c ∧ 0 ≤ R 1 1 ∧ R 1 1 < (N : ℤ)*c
  rw [hRA,hRD,p.1.property.2.1]
  have hs' : ((gamma0CuspTrueWidth N s : ℤ)*c)*gamma0CuspFrequencyStep N s = (N : ℤ)*c := by
    nlinarith [hs]
  have hr' : ((gamma0CuspTrueWidth N r : ℤ)*c)*gamma0CuspFrequencyStep N r = (N : ℤ)*c := by
    nlinarith [hr]
  constructor
  · nlinarith [hA.1]
  constructor
  · nlinarith [hA.2]
  constructor <;> nlinarith [hD.1,hD.2]

theorem gamma0CuspWidthRefinement_injective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Injective (gamma0CuspWidthRefinement N r s c) := by
  rintro ⟨R,l,k⟩ ⟨S,a,b⟩ h
  have he : gamma0TrueWidthDoubleCosetExpand N r s c (R,(l.val : ℤ),(k.val : ℤ)) =
      gamma0TrueWidthDoubleCosetExpand N r s c (S,(a.val : ℤ),(b.val : ℤ)) := by
    apply Subtype.ext
    exact congrArg (fun M : gamma0CuspReducedMatrix N r s c => M.val) h
  have hp := gamma0TrueWidthDoubleCosetExpand_injective N r s c he
  have hR := congrArg Prod.fst hp
  have hl : (l.val : ℤ) = (a.val : ℤ) := congrArg (fun p => p.2.1) hp
  have hk : (k.val : ℤ) = (b.val : ℤ) := congrArg (fun p => p.2.2) hp
  exact Prod.ext hR (Prod.ext (Fin.ext (by exact_mod_cast hl))
    (Fin.ext (by exact_mod_cast hk)))

theorem gamma0CuspWidthRefinement_surjective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Surjective (gamma0CuspWidthRefinement N r s c) := by
  intro M
  let M₀ : gamma0CuspMatrixFibre N r s c := ⟨M.val,M.property.1,M.property.2.1⟩
  obtain ⟨⟨R,l,k⟩,h⟩ := gamma0TrueWidthDoubleCosetExpand_surjective N r s c M₀
  have hA := congrArg (fun T : gamma0CuspMatrixFibre N r s c => T.val 0 0) h
  have hD := congrArg (fun T : gamma0CuspMatrixFibre N r s c => T.val 1 1) h
  change (integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*l) * R.val *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) 0 0 = M.val 0 0 at hA
  change (integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*l) * R.val *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k)) 1 1 = M.val 1 1 at hD
  rw [(integerTranslation_entries _ _ _).1,R.property.2.1] at hA
  rw [(integerTranslation_entries _ _ _).2.2,R.property.2.1] at hD
  have hs : (gamma0CuspTrueWidth N s : ℤ)*gamma0CuspFrequencyStep N s = N := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N s
  have hr : (gamma0CuspTrueWidth N r : ℤ)*gamma0CuspFrequencyStep N r = N := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hL : 0 < (gamma0CuspTrueWidth N s : ℤ)*c := mul_pos
    (by exact_mod_cast gamma0CuspTrueWidth_pos N s) (by exact_mod_cast NeZero.pos c)
  have hK : 0 < (gamma0CuspTrueWidth N r : ℤ)*c := mul_pos
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r) (by exact_mod_cast NeZero.pos c)
  have hl0 : 0 ≤ l := by
    by_contra hn
    have hl1 : l ≤ -1 := by omega
    have hm : 0 ≤ ((gamma0CuspTrueWidth N s : ℤ)*c)*(-1-l) :=
      mul_nonneg hL.le (by omega)
    nlinarith [M.property.2.2.1,R.property.2.2.2.1]
  have hk0 : 0 ≤ k := by
    by_contra hn
    have hk1 : k ≤ -1 := by omega
    have hm : 0 ≤ ((gamma0CuspTrueWidth N r : ℤ)*c)*(-1-k) :=
      mul_nonneg hK.le (by omega)
    nlinarith [M.property.2.2.2.2.1,R.property.2.2.2.2.2]
  have hlq : l < gamma0CuspFrequencyStep N s := by
    by_contra hn
    have hm : 0 ≤ ((gamma0CuspTrueWidth N s : ℤ)*c)*(l-gamma0CuspFrequencyStep N s) :=
      mul_nonneg hL.le (by omega)
    have he : ((gamma0CuspTrueWidth N s : ℤ)*c)*gamma0CuspFrequencyStep N s = (N : ℤ)*c := by
      nlinarith [hs]
    nlinarith [M.property.2.2.2.1,R.property.2.2.1]
  have hkq : k < gamma0CuspFrequencyStep N r := by
    by_contra hn
    have hm : 0 ≤ ((gamma0CuspTrueWidth N r : ℤ)*c)*(k-gamma0CuspFrequencyStep N r) :=
      mul_nonneg hK.le (by omega)
    have he : ((gamma0CuspTrueWidth N r : ℤ)*c)*gamma0CuspFrequencyStep N r = (N : ℤ)*c := by
      nlinarith [hr]
    nlinarith [M.property.2.2.2.2.2,R.property.2.2.2.2.1]
  let a : Fin (gamma0CuspFrequencyStep N s) := ⟨l.toNat,by omega⟩
  let b : Fin (gamma0CuspFrequencyStep N r) := ⟨k.toNat,by omega⟩
  refine ⟨(R,a,b),?_⟩
  apply Subtype.ext
  have ha : (a.val : ℤ) = l := Int.toNat_of_nonneg hl0
  have hb : (b.val : ℤ) = k := Int.toNat_of_nonneg hk0
  change integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*a.val) * R.val *
    integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*b.val) = M.val
  rw [ha,hb]
  exact congrArg Subtype.val h

def gamma0CuspWidthRefinementEquiv (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    (gamma0TrueWidthReducedMatrix N r s c ×
      Fin (gamma0CuspFrequencyStep N s) × Fin (gamma0CuspFrequencyStep N r)) ≃
      gamma0CuspReducedMatrix N r s c :=
  Equiv.ofBijective _ ⟨gamma0CuspWidthRefinement_injective N r s c,
    gamma0CuspWidthRefinement_surjective N r s c⟩

theorem gamma0CuspReducedMatrix_card_trueWidth (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Fintype.card (gamma0CuspReducedMatrix N r s c) =
      Fintype.card (gamma0TrueWidthReducedMatrix N r s c) *
        (gamma0CuspFrequencyStep N s * gamma0CuspFrequencyStep N r) := by
  rw [← Fintype.card_congr (gamma0CuspWidthRefinementEquiv N r s c)]
  simp only [Fintype.card_prod,Fintype.card_fin]

theorem gamma0CuspReducedMatrix_sum_trueWidth (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (F : SL(2, ℤ) → ℂ) :
    (∑ R : gamma0CuspReducedMatrix N r s c, F R.val) =
      ∑ R : gamma0TrueWidthReducedMatrix N r s c,
        ∑ a : Fin (gamma0CuspFrequencyStep N s),
          ∑ b : Fin (gamma0CuspFrequencyStep N r),
            F (integerTranslation ((gamma0CuspTrueWidth N s : ℤ)*a.val) * R.val *
              integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*b.val)) := by
  rw [← Equiv.sum_comp (gamma0CuspWidthRefinementEquiv N r s c) (fun R => F R.val)]
  simp only [Fintype.sum_prod_type]
  rfl

end ArtinMatthews
