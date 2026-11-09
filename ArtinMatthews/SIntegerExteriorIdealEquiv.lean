module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Nonzero ideals of a localization away from d are exactly the
nonzero integral ideals coprime to (d). The equivalence preserves the
actual ideal extension and multiplication. -/

namespace ArtinMatthews.SIntegerPrincipalization
open scoped nonZeroDivisors Classical
open UniqueFactorizationMonoid
noncomputable section

variable {R A : Type*} [CommRing R] [IsDedekindDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Module.IsTorsionFree R A]

def exteriorIdeals (d : R) : Submonoid (Ideal R) where
  carrier := {I | I ≠ ⊥ ∧ IsCoprime I (Ideal.span {d})}
  one_mem' := ⟨one_ne_zero, isCoprime_one_left⟩
  mul_mem' hI hJ := ⟨mul_ne_zero hI.1 hJ.1, hI.2.mul_left hJ.2⟩

omit [IsDedekindDomain R] in
theorem prime_coprime_span_of_not_mem (P : Ideal R) (hP : P.IsMaximal)
    (d : R) (hd : d ∉ P) : IsCoprime P (Ideal.span {d}) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra h
  have he := hP.eq_of_le h le_sup_left
  have hle : Ideal.span {d} ≤ P := le_sup_right.trans_eq he.symm
  exact hd (hle (Ideal.subset_span (by simp)))

omit [IsDedekindDomain R] [IsDomain A] [Module.IsTorsionFree R A] in
theorem away_under_map_of_coprime (d : R) [IsLocalization.Away d A]
    (I : Ideal R) (hc : IsCoprime I (Ideal.span {d})) :
    (I.map (algebraMap R A)).under R = I := by
  apply le_antisymm
  · intro x hx
    obtain ⟨m, hm, hmx⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers d) A I x).mp hx
    obtain ⟨n, rfl⟩ := hm
    have hcn : IsCoprime I (Ideal.span {d ^ n}) := by
      rw [← Ideal.span_singleton_pow]
      exact hc.pow_right
    obtain ⟨a, ha, b, hb, he⟩ := Ideal.isCoprime_iff_exists.mp hcn
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hb
    have hmem : a * x + (d ^ n * x) * t ∈ I :=
      I.add_mem (I.mul_mem_right x ha) (I.mul_mem_right t hmx)
    have heq : a * x + (d ^ n * x) * t = x := by linear_combination x * he
    exact heq ▸ hmem
  · exact Ideal.le_comap_map

def exteriorPart (d : R) (I : Ideal R) : Ideal R :=
  ((normalizedFactors I).filter fun P => IsCoprime P (Ideal.span {d})).prod

theorem exteriorPart_ne_zero (d : R) (I : Ideal R) : exteriorPart d I ≠ ⊥ := by
  apply prod_ne_zero_of_subset_normalizedFactors
  intro P hP
  exact (Multiset.mem_filter.mp hP).1

theorem exteriorPart_coprime (d : R) (I : Ideal R) :
    IsCoprime (exteriorPart d I) (Ideal.span {d}) := by
  have hprod (l : Multiset (Ideal R)) (hl : ∀ P ∈ l, IsCoprime P (Ideal.span {d})) :
      IsCoprime l.prod (Ideal.span {d}) := by
    induction l using Multiset.induction_on with
    | empty => exact isCoprime_one_left
    | cons P l ih =>
      have hhead : IsCoprime P (Ideal.span {d}) := hl P (Multiset.mem_cons_self P l)
      have htail : ∀ Q ∈ l, IsCoprime Q (Ideal.span {d}) :=
        fun Q hQ => hl Q (Multiset.mem_cons_of_mem hQ)
      have ht : IsCoprime l.prod (Ideal.span {d}) := ih htail
      rw [Multiset.prod_cons]
      exact hhead.mul_left ht
  exact hprod _ (fun P hP => (Multiset.mem_filter.mp hP).2)

omit [IsDomain A] [Module.IsTorsionFree R A] in
theorem map_filter_coprime_prod (d : R) [IsLocalization.Away d A]
    (l : Multiset (Ideal R)) (hl : ∀ P ∈ l, Prime P) :
    ((l.filter fun P => IsCoprime P (Ideal.span {d})).prod).map (algebraMap R A) =
      l.prod.map (algebraMap R A) := by
  induction l using Multiset.induction_on with
  | empty => simp
  | cons P l ih =>
    have hP := hl P (Multiset.mem_cons_self _ _)
    have hrest := ih (fun Q hQ => hl Q (Multiset.mem_cons_of_mem hQ))
    by_cases hc : IsCoprime P (Ideal.span {d})
    · rw [Multiset.filter_cons_of_pos (p := fun Q : Ideal R => IsCoprime Q (Ideal.span {d})) l hc,
        Multiset.prod_cons, Multiset.prod_cons,
        Ideal.map_mul, Ideal.map_mul, hrest]
    · have hd : d ∈ P := by
        by_contra hd
        exact hc (prime_coprime_span_of_not_mem P
          ((Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero) d hd)
      have hmap : P.map (algebraMap R A) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hd)
          (IsLocalization.Away.algebraMap_isUnit d)
      rw [Multiset.filter_cons_of_neg (p := fun Q : Ideal R => IsCoprime Q (Ideal.span {d})) l hc,
        Multiset.prod_cons, Ideal.map_mul,
        hmap, ← Ideal.one_eq_top, one_mul]
      exact hrest

omit [IsDomain A] [Module.IsTorsionFree R A] in
theorem exteriorPart_map (d : R) [IsLocalization.Away d A]
    (I : Ideal R) (hI : I ≠ ⊥) :
    (exteriorPart d I).map (algebraMap R A) = I.map (algebraMap R A) := by
  have he : (normalizedFactors I).prod = I := by
    simpa only [normalize_eq] using prod_normalizedFactors_eq hI
  exact (map_filter_coprime_prod d _ (fun P hP => prime_of_normalized_factor P hP)).trans
    (congrArg (fun J : Ideal R => J.map (algebraMap R A)) he)

def awayExteriorIdealMap (d : R) (A : Type*) [CommRing A] [IsDomain A]
    [Algebra R A] [Module.IsTorsionFree R A] : exteriorIdeals d →* (Ideal A)⁰ where
  toFun I := ⟨I.val.map (algebraMap R A), mem_nonZeroDivisors_iff_ne_zero.mpr
    ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R A)).not.mpr I.property.1)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Ideal.mapHom (algebraMap R A))
  map_mul' I J := by
    apply Subtype.ext
    exact map_mul (Ideal.mapHom (algebraMap R A)) I.val J.val

theorem awayExteriorIdealMap_injective (d : R) [IsLocalization.Away d A] :
    Function.Injective (awayExteriorIdealMap d A) := by
  intro I J he
  have h := congrArg (fun B : (Ideal A)⁰ => B.val.under R) he
  change (I.val.map (algebraMap R A)).under R = (J.val.map (algebraMap R A)).under R at h
  rw [away_under_map_of_coprime d I.val I.property.2,
    away_under_map_of_coprime d J.val J.property.2] at h
  exact Subtype.ext h

theorem awayExteriorIdealMap_surjective (d : R) [IsLocalization.Away d A] :
    Function.Surjective (awayExteriorIdealMap d A) := by
  intro J
  have hI : J.val.under R ≠ ⊥ := by
    intro he
    have hm := IsLocalization.map_under (Submonoid.powers d) A J.val
    rw [he, Ideal.map_bot] at hm
    exact (mem_nonZeroDivisors_iff_ne_zero.mp J.property) hm.symm
  refine ⟨⟨exteriorPart d (J.val.under R), exteriorPart_ne_zero d _, exteriorPart_coprime d _⟩, ?_⟩
  apply Subtype.ext
  exact (exteriorPart_map d _ hI).trans (IsLocalization.map_under (Submonoid.powers d) A J.val)

def awayExteriorIdealEquiv (d : R) [IsLocalization.Away d A] : exteriorIdeals d ≃* (Ideal A)⁰ :=
  MulEquiv.ofBijective (awayExteriorIdealMap d A)
    ⟨awayExteriorIdealMap_injective d, awayExteriorIdealMap_surjective d⟩

@[simp] theorem awayExteriorIdealEquiv_apply (d : R) [IsLocalization.Away d A]
    (I : exteriorIdeals d) : (awayExteriorIdealEquiv d I).val = I.val.map (algebraMap R A) := rfl

end
end ArtinMatthews.SIntegerPrincipalization
