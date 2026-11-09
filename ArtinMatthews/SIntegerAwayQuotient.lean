module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact quotient transport for a genuine localization away from d.
The natural map is proved bijective when the modulus is coprime to d;
integral representative coverage is a conclusion. -/
namespace ArtinMatthews.SIntegerQuotient

open scoped Classical
noncomputable section
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem quotient_isUnit_of_coprime (I : Ideal R) (d : R)
    (hc : IsCoprime I (Ideal.span {d})) : IsUnit (Ideal.Quotient.mk I d) := by
  obtain ⟨a,ha,b,hb,he⟩ := Ideal.isCoprime_iff_exists.mp hc
  obtain ⟨t,ht⟩ := Ideal.mem_span_singleton.mp hb
  have h := congrArg (Ideal.Quotient.mk I) he
  rw [map_add, (Ideal.Quotient.eq_zero_iff_mem.mpr ha), zero_add, map_one, ht, map_mul] at h
  exact IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk I t) (by simpa only [mul_comm] using h)

theorem quotient_powers_units (I : Ideal R) (d : R)
    (hc : IsCoprime I (Ideal.span {d})) (s : Submonoid.powers d) :
    IsUnit (Ideal.Quotient.mk I (s : R)) := by
  obtain ⟨n,hn⟩ := s.property
  rw [← hn, map_pow]
  exact (quotient_isUnit_of_coprime I d hc).pow n

def awayQuotientEquiv (d : R) [IsLocalization.Away d A] (I : Ideal R)
    (hc : IsCoprime I (Ideal.span {d})) :
    (R ⧸ I) ≃ₐ[R] A ⧸ I.map (algebraMap R A) := by
  refine AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) ?_) ?_ ?_ ?_
  · intro x hx
    change Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap R A x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
  · refine Ideal.Quotient.liftₐ _
      (IsLocalization.liftAlgHom (M := Submonoid.powers d) (S := A) (f := Ideal.Quotient.mkₐ R I)
        (quotient_powers_units I d hc)) ?_
    have hker : I.map (algebraMap R A) ≤ RingHom.ker
        (IsLocalization.liftAlgHom (M := Submonoid.powers d) (S := A) (f := Ideal.Quotient.mkₐ R I)
          (quotient_powers_units I d hc)).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change IsLocalization.lift (quotient_powers_units I d hc) (algebraMap R A x) = 0
      rw [IsLocalization.lift_eq]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
    exact fun x hx => hker hx
  · rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective _ _)]
    exact IsLocalization.algHom_ext (W := Submonoid.powers d) (A := R) (by ext)
  · rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective _ _)]
    ext

theorem awayQuotientEquiv_mk (d : R) [IsLocalization.Away d A] (I : Ideal R)
    (hc : IsCoprime I (Ideal.span {d})) (x : R) :
    awayQuotientEquiv (A := A) d I hc (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap R A x) := rfl

theorem away_quotient_representative (d : R) [IsLocalization.Away d A] (I : Ideal R)
    (hc : IsCoprime I (Ideal.span {d})) (z : A) :
    ∃ x : R, z - algebraMap R A x ∈ I.map (algebraMap R A) := by
  obtain ⟨x,hx⟩ := (awayQuotientEquiv (A := A) d I hc).surjective (Ideal.Quotient.mk _ z)
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨x, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  rw [map_sub, ← awayQuotientEquiv_mk d I hc, hx, sub_self]

theorem away_quotient_card (d : R) [IsLocalization.Away d A] (I : Ideal R)
    (hc : IsCoprime I (Ideal.span {d})) :
    Nat.card (A ⧸ I.map (algebraMap R A)) = Nat.card (R ⧸ I) :=
  Nat.card_congr (awayQuotientEquiv (A := A) d I hc).toEquiv.symm

theorem away_quotient_finite (d : R) [IsLocalization.Away d A] (I : Ideal R)
    (hc : IsCoprime I (Ideal.span {d})) [Finite (R ⧸ I)] :
    Finite (A ⧸ I.map (algebraMap R A)) :=
  Finite.of_surjective (awayQuotientEquiv (A := A) d I hc) (awayQuotientEquiv (A := A) d I hc).surjective

end
end ArtinMatthews.SIntegerQuotient
