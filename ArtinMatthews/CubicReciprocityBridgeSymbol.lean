module

public import ArtinMatthews.CubicReciprocityBridgeFrobenius
public import ArtinMatthews.CubicReciprocityNonprincipalModel
public import OAI.NumberTheory.CubicGram.SquarefreeGauss


set_option backward.privateInPublic true
@[expose] public section

/-! The two concrete definitions of the cubic residue symbol agree. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.ActualEisensteinCubic
local notation "EO" => OAI.SevenEighths.HeckeFamily.O
local notation "CE" => OAI.CubicFirstMoment.Eisenstein

/-- Comparison through the defining Euler criterion, with the same complex orientation. -/
theorem cubicSymbolAtPrime_eq_actualCubicChar (P : Ideal EO) [P.IsMaximal]
    (hg : lambda ∉ P) {p : EO} (hP : P = Ideal.span {p})
    (hp : CubicFirstMoment.primaryPrime (heckeIntegersEquivCubicEisenstein p))
    {a : EO} (ha : a ∉ P) :
    CubicFirstMoment.cubicSymbolAtPrime (heckeIntegersEquivCubicEisenstein p)
      (heckeIntegersEquivCubicEisenstein a) =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hg (Ideal.Quotient.mk P a)) := by
  classical
  let e := heckeIntegersEquivCubicEisenstein
  let q : CE := e p
  let I : Ideal CE := CubicFirstMoment.modulus q
  have hmap : I = P.map e := by
    rw [hP]
    simp only [I, CubicFirstMoment.modulus, Ideal.map_span, Set.image_singleton, q]
  let eqv := Ideal.quotientEquiv P I e hmap
  have hcard : CubicFirstMoment.normNat q = Nat.card (EO ⧸ P) :=
    (CubicFirstMoment.residues_card hp.2.ne_zero).symm.trans
      (Nat.card_congr eqv.toEquiv).symm
  let : I.IsPrime := by
    change (Ideal.span {q}).IsPrime
    exact (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (CE ⧸ I) := CubicFirstMoment.finite_residues hp.2.ne_zero
  let : Fintype (CE ⧸ I) := Fintype.ofFinite _
  let : Field (CE ⧸ I) := Fintype.fieldOfDomain _
  have haunit : IsUnit (Ideal.Quotient.mk I (e a)) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply ha
    apply (Ideal.Quotient.eq_zero_iff_mem (I := P)).mp
    apply eqv.injective
    change Ideal.Quotient.mk I (e a) = eqv 0
    simpa only [map_zero] using hz
  obtain ⟨j, hj, _⟩ := CubicFirstMoment.cubicSymbol_euler_exists_unique hp haunit
  let y : EO := e.symm (CubicFirstMoment.omegaE ^ (j : ℕ))
  have hy3 : y ^ 3 = 1 := by
    apply e.injective
    simp only [map_pow, y, RingEquiv.apply_symm_apply, map_one]
    rw [← pow_mul, Nat.mul_comm, pow_mul, CubicFirstMoment.omegaE_cube, one_pow]
  have hy : y ∉ P := by
    intro h
    have h1 : (1 : EO) ∈ P := by rw [← hy3]; exact P.pow_mem_of_mem h 3 (by decide)
    exact (inferInstance : P.IsPrime).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hthree : (3 : EO) ∉ P := by
    intro h
    have hsq : lambda ^ 2 ∈ P := by
      have heq : lambda ^ 2 = (-3 : EO) * omega := by
        change (omega - 1) ^ 2 = (-3 : EO) * omega
        linear_combination omega_sq_for_norm
      rw [heq]
      exact P.mul_mem_right _ (P.neg_mem h)
    exact hg ((inferInstance : P.IsPrime).mem_of_pow_mem 2 hsq)
  let c : EO := cubicChar P hg (Ideal.Quotient.mk P a)
  have hc3 : c ^ 3 = 1 := CubicRamified.cubicValue_cube P hg a ha
  have hred : Ideal.Quotient.mk P c = Ideal.Quotient.mk P y := by
    apply eqv.injective
    change Ideal.Quotient.mk I (e c) = Ideal.Quotient.mk I (e y)
    have heuler := congrArg eqv (cubicChar_reduce P hg (Ideal.Quotient.mk P a))
    calc
      Ideal.Quotient.mk I (e c) =
          (Ideal.Quotient.mk I (e a)) ^ ((Nat.card (EO ⧸ P) - 1) / 3) := by
        rw [map_pow] at heuler
        change Ideal.Quotient.mk I (e c) =
          (Ideal.Quotient.mk I (e a)) ^ ((Nat.card (EO ⧸ P) - 1) / 3) at heuler
        exact heuler
      _ = Ideal.Quotient.mk I (CubicFirstMoment.omegaE ^ (j : ℕ)) := by
        change Ideal.Quotient.mk I
          ((e a) ^ ((CubicFirstMoment.normNat q - 1) / 3)) =
          Ideal.Quotient.mk I (CubicFirstMoment.omegaE ^ (j : ℕ)) at hj
        simpa only [hcard, map_pow] using hj
      _ = Ideal.Quotient.mk I (e y) := by simp only [y, RingEquiv.apply_symm_apply]
  have hcy : c = y := cube_roots_eq_of_reduction_eq P hthree hy (hc3.trans hy3.symm) hred
  rw [CubicFirstMoment.cubicSymbol_euler_value hp haunit j hj]
  rw [← heckeIntegersEquivCubicEisenstein_coe]
  change CubicFirstMoment.omega ^ (j : ℕ) = (e c : ℂ)
  rw [hcy]
  simp only [y, RingEquiv.apply_symm_apply, Subalgebra.coe_pow]
  rfl

/-- Prime value of the supplied global cubic symbol is the actual residue character. -/
theorem cubicSymbol_eq_actualCubicChar (P : Ideal EO) [P.IsMaximal]
    (hg : lambda ∉ P) {p : EO} (hP : P = Ideal.span {p})
    (hp : CubicFirstMoment.primaryPrime (heckeIntegersEquivCubicEisenstein p))
    {a : EO} (ha : a ∉ P) :
    CubicFirstMoment.cubicSymbol (heckeIntegersEquivCubicEisenstein p)
      (heckeIntegersEquivCubicEisenstein a) =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hg (Ideal.Quotient.mk P a)) := by
  rw [CubicFirstMoment.cubicSymbol_prime hp]
  exact cubicSymbolAtPrime_eq_actualCubicChar P hg hP hp ha

end ArtinMatthews
