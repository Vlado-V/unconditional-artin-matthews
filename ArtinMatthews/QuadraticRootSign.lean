module

public import ArtinMatthews.TameQuadraticGauss


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical complex sign of an actual square root of unity.  No field
embedding is needed, including when the source field is nonarchimedean. -/

namespace ArtinMatthews.QuadraticGauss

open scoped Classical

noncomputable section

variable (K : Type*) [Field K]

theorem twoRoot_value_cases (z : rootsOfUnity 2 K) :
    ((z : Kˣ) : K) = 1 ∨ ((z : Kˣ) : K) = -1 := by
  apply sq_eq_one_iff.mp
  have hz : (z : Kˣ) ^ 2 = 1 := z.2
  exact congrArg Units.val hz

theorem twoRoot_eq_one_of_value {z : rootsOfUnity 2 K}
    (hz : ((z : Kˣ) : K) = 1) : z = 1 :=
  Subtype.ext (Units.ext hz)

def rootSign : rootsOfUnity 2 K →* ℂ where
  toFun z := if z = 1 then 1 else -1
  map_one' := by simp
  map_mul' z w := by
    by_cases hz : z = 1
    · subst z
      simp
    by_cases hw : w = 1
    · subst w
      simp
    have hzv : ((z : Kˣ) : K) = -1 :=
      (twoRoot_value_cases K z).resolve_left (fun h => hz (twoRoot_eq_one_of_value K h))
    have hwv : ((w : Kˣ) : K) = -1 :=
      (twoRoot_value_cases K w).resolve_left (fun h => hw (twoRoot_eq_one_of_value K h))
    have hzw : z * w = 1 := by
      apply twoRoot_eq_one_of_value K
      change ((z : Kˣ) : K) * ((w : Kˣ) : K) = 1
      rw [hzv, hwv, neg_one_mul, neg_neg]
    simp [hz, hw, hzw]

theorem rootSign_apply (z : rootsOfUnity 2 K) :
    rootSign K z = if z = 1 then 1 else -1 := rfl

theorem rootSign_eq_one_iff (z : rootsOfUnity 2 K) :
    rootSign K z = 1 ↔ z = 1 := by
  by_cases hz : z = 1
  · simp [rootSign_apply, hz]
  · simp [rootSign_apply, hz]
    norm_num

theorem rootSign_injective : Function.Injective (rootSign K) := by
  intro z w he
  by_cases hz : z = 1
  · have hw : w = 1 := (rootSign_eq_one_iff K w).mp (by simpa [hz] using he.symm)
    exact hz.trans hw.symm
  by_cases hw : w = 1
  · exact False.elim (hz ((rootSign_eq_one_iff K z).mp (by simpa [hw] using he)))
  apply Subtype.ext
  apply Units.ext
  exact ((twoRoot_value_cases K z).resolve_left
    (fun h => hz (twoRoot_eq_one_of_value K h))).trans
      ((twoRoot_value_cases K w).resolve_left
        (fun h => hw (twoRoot_eq_one_of_value K h))).symm

theorem rootSign_sq (z : rootsOfUnity 2 K) : rootSign K z ^ 2 = 1 := by
  by_cases hz : z = 1 <;> simp [rootSign_apply, hz]

theorem rootSign_zpow (z : rootsOfUnity 2 K) (m : ℤ) :
    rootSign K (z ^ m) = rootSign K z ^ m := map_zpow _ _ _

end

end ArtinMatthews.QuadraticGauss
