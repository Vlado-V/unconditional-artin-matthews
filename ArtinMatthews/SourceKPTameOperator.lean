module

public import ArtinMatthews.SourceJacquetShellVector
public import Mathlib.RepresentationTheory.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The three-dimensional operator in the tame torus model. Exponents
of cubic phases are evaluated in the actual residue group Z/3Z.
Its composition identity keeps the complete torus multiplier. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def sourceKPCubicPower {A : Type*} [Monoid A] (u : A) (i : ZMod 3) : A :=
  u ^ i.val

theorem sourceKPCubicPower_int {A : Type*} [Group A] (u : A) (hu : u ^ 3 = 1) (j : ℤ) :
    sourceKPCubicPower u (j : ZMod 3) = u ^ j := by
  rw [sourceKPCubicPower, ← zpow_natCast, ZMod.val_intCast]
  change u ^ (j % (3 : ℤ)) = u ^ j
  have h₃ : u ^ (3 : ℤ) = 1 := by exact_mod_cast hu
  calc
    _ = u ^ (j % 3 + 3 * (j / 3)) := by rw [zpow_add, zpow_mul, h₃, one_zpow, mul_one]
    _ = _ := congrArg (fun n : ℤ => u ^ n) (Int.emod_add_mul_ediv j 3)

theorem sourceKPCubicPower_add {A : Type*} [Group A] (u : A) (hu : u ^ 3 = 1) (i j : ZMod 3) :
    sourceKPCubicPower u (i + j) = sourceKPCubicPower u i * sourceKPCubicPower u j := by
  have h : (((i.val : ℤ) + (j.val : ℤ) : ℤ) : ZMod 3) = i + j := by
    simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← h, sourceKPCubicPower_int u hu, zpow_add]
  simp only [sourceKPCubicPower, zpow_natCast]

theorem sourceKPCubicPower_mul {A : Type*} [CommMonoid A] (u v : A) (i : ZMod 3) :
    sourceKPCubicPower (u * v) i = sourceKPCubicPower u i * sourceKPCubicPower v i := mul_pow _ _ _

theorem sourceKPCubicPower_one {A : Type*} [Monoid A] (i : ZMod 3) :
    sourceKPCubicPower (1 : A) i = 1 := one_pow _

theorem sourceKPCubicPower_zero {A : Type*} [Monoid A] (u : A) :
    sourceKPCubicPower u 0 = 1 := by rw [sourceKPCubicPower, ZMod.val_zero, pow_zero]

def sourceKPTameOperator (Q : ℝ) (z u : ℂˣ) (j : ℤ) : Module.End ℂ (ZMod 3 → ℂ) where
  toFun f i := (z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) *
    (sourceKPCubicPower (A := ℂˣ) u ((j : ZMod 3) - 2 * i) : ℂ) * f (i - (j : ZMod 3))
  map_add' f g := by
    funext i
    exact mul_add _ _ _
  map_smul' c f := by
    funext i
    change _ * (c * _) = c * (_ * _)
    ring

theorem sourceKPTameOperator_one (Q : ℝ) : sourceKPTameOperator Q 1 1 0 = 1 := by
  apply LinearMap.ext
  intro f
  funext i
  simp [sourceKPTameOperator, sourceJacquetScale, sourceKPCubicPower_one]
  exact congrArg f (sub_zero i)

theorem sourceKPTameOperator_mul (Q : ℝ) (hQ : 0 < Q) (z w u v : ℂˣ)
    (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (j k : ℤ) :
    sourceKPTameOperator Q (z * w * sourceKPCubicPower (A := ℂˣ) v (j : ZMod 3) *
        sourceKPCubicPower (A := ℂˣ) u (-(k : ZMod 3))) (u * v) (j + k) =
      sourceKPTameOperator Q z u j * sourceKPTameOperator Q w v k := by
  apply LinearMap.ext
  intro f
  funext i
  let J : ZMod 3 := j
  let K : ZMod 3 := k
  let qj := sourceJacquetScale Q ((j : ℝ) / 6)
  let qk := sourceJacquetScale Q ((k : ℝ) / 6)
  have hQsum : sourceJacquetScale Q (((j + k : ℤ) : ℝ) / 6) = qj * qk := by
    rw [Int.cast_add, add_div, sourceJacquetScale_add hQ]
  have hJK : ((j + k : ℤ) : ZMod 3) = J + K := Int.cast_add _ _
  have hshift : i - (J + K) = (i - J) - K := by ring
  have hU : (sourceKPCubicPower (A := ℂˣ) u (-K) : ℂ) *
      (sourceKPCubicPower (A := ℂˣ) u (J + K - 2 * i) : ℂ) =
        (sourceKPCubicPower (A := ℂˣ) u (J - 2 * i) : ℂ) := by
    rw [← Units.val_mul, ← sourceKPCubicPower_add u hu]
    have h : -K + (J + K - 2 * i) = J - 2 * i := by abel
    rw [h]
  have hV : (sourceKPCubicPower (A := ℂˣ) v J : ℂ) *
      (sourceKPCubicPower (A := ℂˣ) v (J + K - 2 * i) : ℂ) =
        (sourceKPCubicPower (A := ℂˣ) v (K - 2 * (i - J)) : ℂ) := by
    rw [← Units.val_mul, ← sourceKPCubicPower_add v hv]
    congr 2
    ring
  change ((z * w * sourceKPCubicPower (A := ℂˣ) v J * sourceKPCubicPower (A := ℂˣ) u (-K) : ℂˣ) : ℂ) *
        sourceJacquetScale Q (((j + k : ℤ) : ℝ) / 6) *
        (sourceKPCubicPower (A := ℂˣ) (u * v) (((j + k : ℤ) : ZMod 3) - 2 * i) : ℂ) *
          f (i - ((j + k : ℤ) : ZMod 3)) =
      (z : ℂ) * qj * (sourceKPCubicPower (A := ℂˣ) u (J - 2 * i) : ℂ) *
        ((w : ℂ) * qk * (sourceKPCubicPower (A := ℂˣ) v (K - 2 * (i - J)) : ℂ) * f ((i - J) - K))
  rw [hQsum, hJK, sourceKPCubicPower_mul (A := ℂˣ), hshift]
  simp only [Units.val_mul]
  rw [← hU, ← hV]
  ring

end
end ArtinMatthews
