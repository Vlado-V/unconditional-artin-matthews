module

public import ArtinMatthews.MarkedTypeIIFourier
public import ArtinMatthews.MarkedMajorUnitSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Literal six-character expansion of the rational determinant phase on
actual natural-number coordinates, with no assumed Fourier decomposition. -/
namespace ArtinMatthews
open Finset
noncomputable section

def markedMajorIntegerDeterminant (z z' : ℕ×(ℕ×ℕ)) : ℤ :=
  (z.1:ℤ)*z.2.1*z.2.2-(z'.1:ℤ)*z'.2.1*z'.2.2

def markedMajorIntegerArcPhase (q : ℕ) (h : ℤ) (z z' : ℕ×(ℕ×ℕ)) : ℂ :=
  Complex.exp (Complex.I*((2*Real.pi*(h:ℝ)*
    ((markedMajorIntegerDeterminant z z'-(z.1:ℤ)+(z'.1:ℤ):ℤ):ℝ)/(q:ℝ):ℝ):ℂ))

def markedMajorCharacterLeft (q : ℕ) [NeZero q]
    (χ : AddChar (MarkedUnitTuple q) ℂ) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  markedCoordinateDirichlet q χ 1 z.1 * markedCoordinateDirichlet q χ 2 z.2.1 *
    markedCoordinateDirichlet q χ 3 z.2.2

def markedMajorCharacterRight (q : ℕ) [NeZero q]
    (χ : AddChar (MarkedUnitTuple q) ℂ) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  markedCoordinateDirichlet q χ 0 z.1 * markedCoordinateDirichlet q χ 4 z.2.1 *
    markedCoordinateDirichlet q χ 5 z.2.2

theorem markedMajor_character_phase (q : ℕ) [NeZero q] (h : ℤ)
    (z z' : ℕ×(ℕ×ℕ))
    (hz : IsUnit (z.1:ZMod q) ∧ IsUnit (z.2.1:ZMod q) ∧ IsUnit (z.2.2:ZMod q))
    (hz' : IsUnit (z'.1:ZMod q) ∧ IsUnit (z'.2.1:ZMod q) ∧ IsUnit (z'.2.2:ZMod q)) :
    markedMajorIntegerArcPhase q h z z' =
      ∑ χ : AddChar (MarkedUnitTuple q) ℂ,
        markedFourierCoeff (markedResiduePhase q h) χ*
          markedMajorCharacterLeft q χ z*markedMajorCharacterRight q χ z' := by
  classical
  let v : Fin 6 → ℕ := ![z'.1,z.1,z.2.1,z.2.2,z'.2.1,z'.2.2]
  have hv : ∀ i : Fin 6,IsUnit (v i:ZMod q) := by
    intro i
    fin_cases i <;> dsimp [v] <;> tauto
  let x : MarkedUnitTuple q := fun i => Additive.ofMul (hv i).unit
  have hx : ∀ i : Fin 6,((v i:ℤ):ZMod q)=(Additive.toMul (x i)).val := by
    intro i
    dsimp [x]
    simp only [Int.cast_natCast]
  have he := marked_integer_phase_eq q h (fun i => (v i:ℤ)) x hx
  have hphase : markedMajorIntegerArcPhase q h z z' = markedResiduePhase q h x := by
    simpa [markedMajorIntegerArcPhase,markedMajorIntegerDeterminant,v] using he
  rw [hphase,(markedResiduePhase_fourier q h).1 x]
  apply sum_congr rfl
  intro χ _
  rw [marked_tuple_character_eq_dirichlet_product]
  have hcoord (i : Fin 6) : (Additive.toMul (x i)).val=(v i:ZMod q) := by
    simpa only [Int.cast_natCast] using (hx i).symm
  simp only [hcoord]
  norm_num [Fin.prod_univ_succ,v,markedMajorCharacterLeft,markedMajorCharacterRight]
  ring

end
end ArtinMatthews
