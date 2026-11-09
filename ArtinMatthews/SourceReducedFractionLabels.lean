module

public import ArtinMatthews.SourceElementExponents
public import ArtinMatthews.StandardAdelicSIntegerPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Literal reduced fractions in the additive quotient of the source
field by its actual S-integers. The denominator family may in particular
be the balanced allowed generators or the fixed multiplicative ones. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain AllowedGenerators StandardAdelic
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀

abbrev SourceReducedFractionLabel (a : E → R) := Σ e : E, (R ⧸ Ideal.span {a e})ˣ

def sourceAdditiveIntegerSubgroup : AddSubgroup F :=
  ((S : Set (HeightOneSpectrum (𝓞 F))).integer F).toSubring.toAddSubgroup

def sourceReducedFractionValue (a : E → R) (p : SourceReducedFractionLabel F S₀ a) : F :=
  ((Quotient.out (p.2 : R ⧸ Ideal.span {a p.1}) : R) : F) / (a p.1 : F)

def sourceReducedFractionClass (a : E → R) (p : SourceReducedFractionLabel F S₀ a) :
    F ⧸ sourceAdditiveIntegerSubgroup F S₀ :=
  QuotientAddGroup.mk (sourceReducedFractionValue F S₀ a p)

private theorem sourceReducedFraction_cross {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    {d e r : R} (he : (d : F) / (a : F) - (e : F) / (b : F) = (r : F)) :
    d * b - e * a = r * (a * b) := by
  have haF : (a : F) ≠ 0 := fun h => ha (Subtype.ext h)
  have hbF : (b : F) ≠ 0 := fun h => hb (Subtype.ext h)
  apply Subtype.ext
  change (d : F) * (b : F) - (e : F) * (a : F) = (r : F) * ((a : F) * (b : F))
  rw [← he]
  field_simp

private theorem sourceReducedFraction_denom_le {a b d e r : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : IsUnit (Ideal.Quotient.mk (Ideal.span {a}) d))
    (he : (d : F) / (a : F) - (e : F) / (b : F) = (r : F)) :
    Ideal.span {b} ≤ Ideal.span {a} := by
  let I : Ideal R := Ideal.span {a}
  let q := Ideal.Quotient.mk I
  have hzero : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton a))
  have hh := congrArg q (sourceReducedFraction_cross F S₀ ha hb he)
  simp only [map_sub, map_mul, hzero, mul_zero, zero_mul, sub_zero] at hh
  exact (Ideal.span_singleton_le_iff_mem I).mpr
    (Ideal.Quotient.eq_zero_iff_mem.mp (hd.mul_right_eq_zero.mp hh))

/-- Equality modulo the S-integers forces equality of both the exterior
ideal and the reduced residue. This uses arbitrary actual residue lifts. -/
theorem sourceReducedFraction_eq_of_lifts_sub_eq (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e})
    (p q : SourceReducedFractionLabel F S₀ a) (x y r : R)
    (hx : Ideal.Quotient.mk (Ideal.span {a p.1}) x = (p.2 : R ⧸ Ideal.span {a p.1}))
    (hy : Ideal.Quotient.mk (Ideal.span {a q.1}) y = (q.2 : R ⧸ Ideal.span {a q.1}))
    (he : (x : F) / (a p.1 : F) - (y : F) / (a q.1 : F) = (r : F)) : p = q := by
  rcases p with ⟨i, u⟩
  rcases q with ⟨j, v⟩
  have hxu : IsUnit (Ideal.Quotient.mk (Ideal.span {a i}) x) := hx.symm ▸ u.isUnit
  have hyv : IsUnit (Ideal.Quotient.mk (Ideal.span {a j}) y) := hy.symm ▸ v.isUnit
  have h₁ := sourceReducedFraction_denom_le F S₀ (ha i) (ha j) hxu he
  have he' : (y : F) / (a j : F) - (x : F) / (a i : F) = ((-r : R) : F) := by
    change (y : F) / (a j : F) - (x : F) / (a i : F) = -(r : F)
    rw [← he, neg_sub]
  have h₂ := sourceReducedFraction_denom_le F S₀ (ha j) (ha i) hyv he'
  have hij : i = j := (sourcePrimeExponentRingIdealEquiv F S₀).injective
    (Subtype.ext ((hgen i).trans ((le_antisymm h₂ h₁).trans (hgen j).symm)))
  subst j
  have haF : (a i : F) ≠ 0 := fun h => ha i (Subtype.ext h)
  have hxy : x - y = r * a i := by
    apply Subtype.ext
    change (x : F) - (y : F) = (r : F) * (a i : F)
    rw [← he, ← sub_div, div_mul_cancel₀ _ haF]
  have hq := congrArg (Ideal.Quotient.mk (Ideal.span {a i})) hxy
  rw [map_sub, map_mul, hx, hy,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton (a i))), mul_zero] at hq
  exact congrArg (Sigma.mk i) (Units.ext (sub_eq_zero.mp hq))

theorem sourceReducedFractionClass_injective (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e}) :
    Function.Injective (sourceReducedFractionClass F S₀ a) := by
  intro p q h
  have hr : sourceReducedFractionValue F S₀ a p - sourceReducedFractionValue F S₀ a q ∈
      sourceAdditiveIntegerSubgroup F S₀ := QuotientAddGroup.eq_iff_sub_mem.mp h
  let r : R := ⟨_, hr⟩
  exact sourceReducedFraction_eq_of_lifts_sub_eq F S₀ a ha hgen p q _ _ r
    (Ideal.Quotient.mk_out _) (Ideal.Quotient.mk_out _) rfl

theorem sourceReducedFractionClass_zero (a : E → R)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e})
    (p : SourceReducedFractionLabel F S₀ a) (hp : p.1 = 0) :
    sourceReducedFractionClass F S₀ a p = 0 := by
  have ha : Ideal.span {a p.1} = (⊤ : Ideal R) := by
    rw [← hgen, sourcePrimeExponentRingIdealEquiv_val, hp, sourcePrimeExponentIdeal_zero,
      Ideal.one_eq_top, Ideal.map_top]
  have hau : IsUnit (a p.1) := Ideal.span_singleton_eq_top.mp ha
  obtain ⟨u, hu⟩ := hau
  let x := Quotient.out (p.2 : R ⧸ Ideal.span {a p.1})
  let r : R := x * ((u⁻¹ : Rˣ) : R)
  have hr : sourceReducedFractionValue F S₀ a p = (r : F) := by
    change (x : F) / (a p.1 : F) = (x : F) * (((u⁻¹ : Rˣ) : R) : F)
    rw [← hu, div_eq_mul_inv]
    congr 1
    have hh := congrArg (fun z : R => (z : F)) u.mul_inv
    change ((u : R) : F) * (((u⁻¹ : Rˣ) : R) : F) = 1 at hh
    exact inv_eq_of_mul_eq_one_right hh
  change QuotientAddGroup.mk (sourceReducedFractionValue F S₀ a p) = QuotientAddGroup.mk (0 : F)
  rw [QuotientAddGroup.eq_iff_sub_mem, sub_zero, hr]
  exact r.property

end
end ArtinMatthews.SourcePhysical
