module

public import ArtinMatthews.DavenportHasseMonicEnumeration
public import ArtinMatthews.DavenportHasseRootFibers


set_option backward.privateInPublic true
@[expose] public section

/-! The actual lifted Gauss sum is the irreducible prime-power trace of
the multiplicative polynomial weight. This is the finite-field side of
the Davenport--Hasse logarithmic-derivative comparison. -/
namespace ArtinMatthews.DavenportHasse
open Polynomial IntermediateField
open scoped Classical BigOperators
noncomputable section
variable (F E : Type*) [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E]

def representedIrreducibles : Finset F[X] := Finset.univ.image (minpoly F : E → F[X])

theorem mem_representedIrreducibles (P : F[X]) :
    P ∈ representedIrreducibles F E ↔ P.Monic ∧ Irreducible P ∧ P.natDegree ∣ Module.finrank F E := by
  constructor
  · intro h
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp h
    exact ⟨minpoly.monic (IsIntegral.of_finite F x),minpoly.irreducible (IsIntegral.of_finite F x),
      minpoly.degree_dvd (IsIntegral.of_finite F x)⟩
  · rintro ⟨hm,hi,hd⟩
    have hpos : 0 < Nat.card {x : E // minpoly F x=P} := by
      rw [minpolyFiber_card_of_dvd F E P hi hm hd]
      exact hi.natDegree_pos
    obtain ⟨x,hx⟩ := (Nat.card_pos_iff.mp hpos).1
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩

theorem representedIrreducibles_eq :
    representedIrreducibles F E = irreducibleDegreeDivisors (F := F) (Module.finrank F E) := by
  ext P
  rw [mem_representedIrreducibles,mem_irreducibleDegreeDivisors _ Module.finrank_pos]

theorem minpolyFiber_filter_card (P : F[X]) (hP : P ∈ representedIrreducibles F E) :
    (Finset.univ.filter (fun x : E => minpoly F x=P)).card = P.natDegree := by
  obtain ⟨hm,hi,hd⟩ := (mem_representedIrreducibles F E P).mp hP
  have h := minpolyFiber_card_of_dvd F E P hi hm hd
  rw [Nat.card_eq_fintype_card] at h
  exact (Fintype.card_of_subtype _ (by intro x; simp only [Finset.mem_filter,Finset.mem_univ,true_and])).symm.trans h

theorem lifted_gauss_eq_primePowerTrace (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum (FiniteFieldCharacter.normLift F E χ) (FiniteFieldCharacter.traceLift F E ψ) =
      primePowerTrace (polynomialWeight χ ψ) (Module.finrank F E) := by
  let w : F[X] → ℂ := fun P => polynomialWeight χ ψ P ^ (Module.finrank F E / P.natDegree)
  have hf := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset E))
    (t := representedIrreducibles F E) (g := minpoly F)
    (fun x _ => Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩) w
  calc
    _ = ∑ x : E, w (minpoly F x) := by
      rw [lifted_gauss_eq_minpoly_sum F E χ ψ]
      apply Finset.sum_congr rfl
      intro x _
      rw [relativeDegree_eq_div_minpoly F E x]
    _ = ∑ P ∈ representedIrreducibles F E,
        ((Finset.univ.filter (fun x : E => minpoly F x=P)).card : ℂ) * w P := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using hf.symm
    _ = ∑ P ∈ representedIrreducibles F E, (P.natDegree : ℂ)*w P := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [minpolyFiber_filter_card F E P hP]
    _ = _ := by rw [representedIrreducibles_eq]; rfl

end
end ArtinMatthews.DavenportHasse
