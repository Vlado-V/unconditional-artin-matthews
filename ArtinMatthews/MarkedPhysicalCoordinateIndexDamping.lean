module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexTerm
public import ArtinMatthews.MarkedPhysicalInactiveDamping


set_option backward.privateInPublic true
@[expose] public section

/-! The true per-copy term is its root-independent complex coefficient
times the original zero-extended physical damping and good guard. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPhysicalMomentDampingPathTerm {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (pads : ℕ) (Z : Finset (ℤ × ℤ)) (q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (n : ℕ)
    (p : Fin (n+1) → MarkedPhysicalState P (pads+1) Z) : ℂ :=
  if (p 0).1.1=(p (Fin.last n)).1.1 ∧ (∀ v,G (p v)) then
    ∏ v : Fin n,(markedPhysicalEndpointDamping P (pads+1) q (p v.castSucc).1.1.1:ℂ)*
      (markedPhysicalEndpointDamping P (pads+1) q (p v.succ).1.1.1:ℂ)
  else 0

def markedPhysicalCoordinateIndexDamping {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (pads : ℕ) (Z : Finset (ℤ × ℤ)) (q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) {n B : ℕ}
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n B)
    {S : ℕ} {A B' C D : ℝ} (r : MarkedPhysicalCanonicalRoot S A B' C D) : ℂ :=
  markedPhysicalPathCoordinateTerm (markedPhysicalMomentDampingPathTerm P pads Z q G n)
    i.1 r (fun v => (i.2.1 v).1)

theorem markedPhysicalState_damping_unitInterval {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (q : ℝ)
    (hq0 : 0≤q) (hq1 : q≤1) (s : MarkedPhysicalState P M Z) :
    0 ≤ markedPhysicalEndpointDamping P M q s.1.1.1 ∧ markedPhysicalEndpointDamping P M q s.1.1.1≤1 := by
  rw [markedPhysicalEndpointDamping_eq_inactive P M q hq0 Z s]
  refine ⟨markedPhysicalInactivePrimeWeight_nonneg P _ (Real.sqrt_nonneg q) _,
    markedPhysicalInactivePrimeWeight_le_one P _ (Real.sqrt_nonneg q) ?_ _⟩
  exact Real.sqrt_le_iff.mpr ⟨by norm_num,by simpa using hq1⟩

theorem markedPhysicalMomentDampingPathTerm_norm_le_one {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (pads : ℕ) (Z : Finset (ℤ × ℤ)) (q : ℝ)
    (hq0 : 0≤q) (hq1 : q≤1) (G : MarkedPhysicalState P (pads+1) Z → Prop)
    (n : ℕ) (p : Fin (n+1) → MarkedPhysicalState P (pads+1) Z) :
    ‖markedPhysicalMomentDampingPathTerm P pads Z q G n p‖≤1 := by
  unfold markedPhysicalMomentDampingPathTerm
  split_ifs
  · rw [norm_prod]
    apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro v _
    have hs := markedPhysicalState_damping_unitInterval P (pads+1) Z q hq0 hq1 (p v.castSucc)
    have ht := markedPhysicalState_damping_unitInterval P (pads+1) Z q hq0 hq1 (p v.succ)
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg hs.1,abs_of_nonneg ht.1]
    exact (mul_le_mul hs.2 ht.2 ht.1 (by norm_num : (0:ℝ)≤1)).trans_eq (by ring)
  · norm_num

theorem markedPhysicalCoordinateIndexDamping_norm_le_one {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (pads : ℕ) (Z : Finset (ℤ × ℤ)) (q : ℝ)
    (hq0 : 0≤q) (hq1 : q≤1) (G : MarkedPhysicalState P (pads+1) Z → Prop)
    {n B : ℕ} (i : MarkedPhysicalCoordinateIndex P (pads+1) n B)
    {S : ℕ} {A B' C D : ℝ} (r : MarkedPhysicalCanonicalRoot S A B' C D) :
    ‖markedPhysicalCoordinateIndexDamping P pads Z q G i r‖≤1 := by
  unfold markedPhysicalCoordinateIndexDamping markedPhysicalPathCoordinateTerm markedPhysicalPositionPathExtend
  split_ifs with hp
  · dsimp only
    unfold markedPhysicalPathArrayExtend
    split_ifs
    · exact markedPhysicalMomentDampingPathTerm_norm_le_one P pads Z q hq0 hq1 G n _
    · norm_num
  · norm_num

end
end ArtinMatthews
