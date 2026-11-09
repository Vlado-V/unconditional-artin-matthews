module

public import ArtinMatthews.MarkedFiniteEvenMomentPaths
public import ArtinMatthews.MarkedPhysicalMomentTrace


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine constant-mass physical even moment, expanded over all
physical states at all visits, with only endpoint positions identified. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

abbrev MarkedPhysicalMomentPath {J : Type*} (P : J → Finset ℕ)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (R : ℕ) :=
  Fin (2*R+1) → MarkedPhysicalState P M Z

theorem markedPhysicalPositionMoment_paths
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ) (hV : ∀ j,0≤V j)
    (A : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ) (R : ℕ) :
    markedPhysicalPositionMoment P M Z V A R =
      markedPhysicalMass V M *
        (∑ p : MarkedPhysicalMomentPath P M Z R,
          if (p 0).1.1=(p (Fin.last (2*R))).1.1 then
            markedMatrixPathWeight (markedAlternatingMatrix A) (2*R) 0 p else 0).re := by
  rw [markedPhysicalPositionMoment_eq_original_mass P M Z V hV A R]
  congr 1
  exact markedEvenMoment_position_trace_paths A
    (fun s : MarkedPhysicalState P M Z => s.1.1) R

theorem markedPhysicalMomentPath_primitive {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (R : ℕ)
    (p : MarkedPhysicalMomentPath P M Z R) (v : Fin (2*R+1)) :
    IsCoprime (p v).1.1.1.1 (p v).1.1.1.2 := (p v).2.1

theorem markedPhysicalMomentPath_distinct_lists {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (R : ℕ)
    (p : MarkedPhysicalMomentPath P M Z R) (v : Fin (2*R+1)) :
    MarkedPhysicalMarkingDistinct (p v).1.2 := (p v).2.2.1

theorem markedPhysicalMomentPath_active_divides {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (R : ℕ)
    (p : MarkedPhysicalMomentPath P M Z R) (v : Fin (2*R+1)) (j : J) (k : Fin M) :
    (((p v).1.2 j k : ℕ):ℤ)∣(p v).1.1.1.1 := (p v).2.2.2 j k

end
end ArtinMatthews
