module

public import ArtinMatthews.DoubleVoronoiDualAverage


set_option backward.privateInPublic true
@[expose] public section

/-! The actual circle and congruence detector, including the invertible
change of the congruence character needed for the printed numerators. -/
namespace ArtinMatthews
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman.PrimePower
noncomputable section
attribute [local instance] Classical.decEq

theorem doubleVoronoi_lifted_character (H d : ℕ) [NeZero H] [NeZero d]
    (base x : ZMod (H*d)) (j : ZMod d) :
    ZMod.stdAddChar (base+(H : ZMod (H*d))*(j.val : ZMod (H*d))*x) =
      ZMod.stdAddChar base * ZMod.stdAddChar (j*reduction H d x) := by
  rw [AddChar.map_add_eq_mul, mul_assoc, standard_character_reduction]
  rw [map_mul, map_natCast, ZMod.natCast_zmod_val]

/-- Multiplying the d-character index by a reduced unit leaves the entire
finite detector unchanged; no primitivity estimate is used. -/
theorem doubleVoronoi_detector_rescale (H d : ℕ) [NeZero H] [NeZero d]
    (v : (ZMod (H*d))ˣ) (base x : ZMod (H*d)) :
    (∑ j : ZMod d, ZMod.stdAddChar (base+(H : ZMod (H*d))*(j.val : ZMod (H*d))*x)) =
    ∑ j : ZMod d, ZMod.stdAddChar
      (base+(H : ZMod (H*d))*(j.val : ZMod (H*d))*((v : ZMod (H*d))*x)) := by
  simp_rw [doubleVoronoi_lifted_character]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  have h := Equiv.sum_comp (ZMod.unitsMap (dvd_mul_left d H) v).mulRight
    (fun j : ZMod d => ZMod.stdAddChar (j*reduction H d x))
  simpa only [Units.mulRight_apply, mul_assoc, reduction, map_mul,
    ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_ofClass] using h.symm

/-- Source phase with precisely the two Voronoi numerators, together with
its constant detection factor. -/
def doubleVoronoiPrimalPhase (H d : ℕ) (hdH : d∣H)
    (v₃ v₄ a : (ZMod (H*d))ˣ) (k₁ k₂ : ZMod (H*d)) (j : ZMod d) : ZMod (H*d) :=
  let h : ZMod (H*d) := (H : ZMod (H*d))*(j.val : ZMod (H*d))
  (↑(v₄*a*shiftUnit 1 h (circleCorrection_square_zero H d hdH j)) : ZMod (H*d))*k₁ +
    (↑(-(v₃*a)) : ZMod (H*d))*k₂ +
    ((v₃ : ZMod (H*d))-(v₄ : ZMod (H*d)))*(a : ZMod (H*d)) -
    h*(v₄ : ZMod (H*d))*(a : ZMod (H*d))

/-- The original determinant and k1≡1(mod d) detector is exactly the
averaged source phase used by double Voronoi summation. -/
theorem doubleVoronoi_primal_detection (H d : ℕ) [NeZero H] [NeZero d]
    (hdH : d∣H) (v₃ v₄ a : (ZMod (H*d))ˣ) (k₁ k₂ : ZMod (H*d)) :
    (∑ j : ZMod d, ZMod.stdAddChar
      ((a : ZMod (H*d))*((v₄ : ZMod (H*d))*(k₁-1)-(v₃ : ZMod (H*d))*(k₂-1)) +
        (H : ZMod (H*d))*(j.val : ZMod (H*d))*(k₁-1))) =
      ∑ j : ZMod d, ZMod.stdAddChar (doubleVoronoiPrimalPhase H d hdH v₃ v₄ a k₁ k₂ j) := by
  rw [doubleVoronoi_detector_rescale H d (v₄*a)]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [doubleVoronoiPrimalPhase, Units.val_mul, Units.val_neg,
    shiftUnit_val, Units.val_one]
  ring

end
end ArtinMatthews
