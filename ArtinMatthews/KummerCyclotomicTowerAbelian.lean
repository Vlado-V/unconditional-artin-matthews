module

public import ArtinMatthews.KummerCyclotomicTowerCyclic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compositum is abelian over the original Kummer field, by
injective restriction into the auxiliary cyclotomic Galois group. -/

noncomputable section
namespace ArtinMatthews

/-- Fixing the auxiliary cyclotomic field and the radical fixes the compositum. -/
theorem twelfthKummer_aut_eq_one (q : ℕ) (a : ℤ)
    (σ : Gal(twelfthKummerField q a/ℚ))
    (hF : ∀ x : twelfthCyclotomicField q,
      σ (algebraMap (twelfthCyclotomicField q) (twelfthKummerField q a) x) =
        algebraMap (twelfthCyclotomicField q) (twelfthKummerField q a) x)
    (hα : σ (twelfthRadicalRoot q a) = twelfthRadicalRoot q a) : σ = 1 := by
  have heq : σ.toAlgHom = (1 : Gal(twelfthKummerField q a/ℚ)).toAlgHom := by
    apply IntermediateField.algHom_ext_of_eq_adjoin ℚ
      (IntermediateField.restrictScalars_adjoin ℚ (twelfthCyclotomicField q)
        {primeRadicalRoot q a})
    intro x hx
    rcases hx with hx | hx
    · exact hF ⟨x, hx⟩
    · have hx' := Set.mem_singleton_iff.mp hx
      subst x
      exact hα
  exact AlgEquiv.ext (fun x => AlgHom.congr_fun heq x)

/-- Actual restriction of automorphisms over K_q to F_q. -/
def twelfthKummerRestriction (q : ℕ) (a : ℤ) [NeZero q] :
    Gal(twelfthKummerField q a/primeKummerField q a) →*
      Gal(twelfthCyclotomicField q/ℚ) :=
  IntermediateField.restrictRestrictAlgEquivMapHom ℚ
    (twelfthCyclotomicField q) (primeKummerField q a) (twelfthKummerField q a)

/-- Restriction is injective because K_q and F_q generate the actual compositum. -/
theorem twelfthKummerRestriction_injective (q : ℕ) (a : ℤ) [NeZero q] :
    Function.Injective (twelfthKummerRestriction q a) := by
  apply (injective_iff_map_eq_one _).mpr
  intro σ hσ
  apply AlgEquiv.restrictScalars_injective ℚ
  apply twelfthKummer_aut_eq_one
  · intro x
    change (σ.restrictScalars ℚ).restrictNormal (twelfthCyclotomicField q) = 1 at hσ
    rw [← AlgEquiv.restrictNormal_commutes, hσ, AlgEquiv.one_apply]
  · change σ (algebraMap (primeKummerField q a) (twelfthKummerField q a)
      (kummerRadicalRoot q a)) = algebraMap (primeKummerField q a) (twelfthKummerField q a)
        (kummerRadicalRoot q a)
    exact σ.commutes (kummerRadicalRoot q a)

instance twelfthKummerField_isAbelianGalois_over_kummer
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    IsAbelianGalois (primeKummerField q a) (twelfthKummerField q a) := by
  let : IsMulCommutative Gal(twelfthKummerField q a/primeKummerField q a) :=
    .of_comm fun σ τ => twelfthKummerRestriction_injective q a (by
      rw [map_mul, map_mul, mul_comm'])
  exact {}

end ArtinMatthews
