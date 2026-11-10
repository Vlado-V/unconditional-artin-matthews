module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import ArtinMatthews.DavenportHasseRootWeight


set_option backward.privateInPublic true
@[expose] public section

/-! Exact multiplicities in the minimal-polynomial decomposition of a
finite-field Gauss sum. A monic irreducible polynomial of degree d has
exactly d roots in an extension whose degree is divisible by d. -/
namespace ArtinMatthews.DavenportHasse
open Polynomial IntermediateField
open scoped Classical BigOperators
noncomputable section
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Finite E]

def minpolyFiberEquivHom (P : F[X]) (hP : Irreducible P) (hm : P.Monic) :
    {x : E // minpoly F x=P} ≃ (AdjoinRoot P →ₐ[F] E) := by
  have heq (x : E) : minpoly F x=P ↔ x ∈ P.aroots E := by
    rw [Polynomial.mem_aroots]
    constructor
    · intro h
      refine ⟨hP.ne_zero,?_⟩
      rw [← h]
      exact minpoly.aeval F x
    · intro hx
      have he := minpoly.eq_of_irreducible_of_monic hP hx.2 hm
      exact he.symm
  exact (Equiv.subtypeEquivRight heq).trans (AdjoinRoot.equiv E F P hP.ne_zero).symm

theorem minpolyFiber_card_of_dvd (P : F[X]) (hP : Irreducible P) (hm : P.Monic)
    (hd : P.natDegree ∣ Module.finrank F E) :
    Nat.card {x : E // minpoly F x=P} = P.natDegree := by
  let : Fact (Irreducible P) := ⟨hP⟩
  have hf : Module.finrank F (AdjoinRoot P) = P.natDegree := finrank_quotient_span_eq_natDegree
  calc
    _ = Nat.card (AdjoinRoot P →ₐ[F] E) := Nat.card_congr (minpolyFiberEquivHom F E P hP hm)
    _ = Module.finrank F (AdjoinRoot P) :=
      FiniteField.natCard_algHom_of_finrank_dvd (by simpa only [hf] using hd)
    _ = P.natDegree := hf

theorem minpolyFiber_card_of_not_dvd (P : F[X])
    (hd : ¬P.natDegree ∣ Module.finrank F E) :
    Nat.card {x : E // minpoly F x=P} = 0 := by
  have : IsEmpty {x : E // minpoly F x=P} := ⟨fun x => hd (by
    rw [← x.2]
    exact minpoly.degree_dvd (IsIntegral.of_finite F x.1))⟩
  exact Nat.card_eq_zero.mpr (Or.inl this)

theorem minpolyFiber_card (P : F[X]) (hP : Irreducible P) (hm : P.Monic) :
    Nat.card {x : E // minpoly F x=P} =
      if P.natDegree ∣ Module.finrank F E then P.natDegree else 0 := by
  split_ifs with h
  · exact minpolyFiber_card_of_dvd F E P hP hm h
  · exact minpolyFiber_card_of_not_dvd F E P h

theorem relativeDegree_eq_div_minpoly (x : E) :
    Module.finrank F⟮x⟯ E = Module.finrank F E / (minpoly F x).natDegree := by
  have h := minpoly_degree_times_relativeDegree F E x
  rw [← h,Nat.mul_div_cancel_left _ (minpoly.natDegree_pos (IsIntegral.of_finite F x))]

end
end ArtinMatthews.DavenportHasse
