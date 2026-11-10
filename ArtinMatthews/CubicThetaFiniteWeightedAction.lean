module

public import ArtinMatthews.CubicThetaFiniteTest
public import ArtinMatthews.CubicThetaSymplecticEmbedding
public import ArtinMatthews.CubicThetaFiniteLatticeCoset
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite Weil operator is scalar on residue weights invariant
under the lower-right entry of a congruence matrix. The operator's lattice
and coset conditions are all discharged from the integer level condition. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators MatrixGroups Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction

/-- Determinant one makes the lower-right entry a unit modulo the level. -/
theorem cubicTheta_lowerRight_zmod_isUnit (M : ℕ) (γ : SL(2, ℤ))
    (hc : (M : ℤ) ∣ γ 1 0) : IsUnit (γ 1 1 : ZMod M) := by
  have hz : (γ 1 0 : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have hd : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have he : (γ 0 0 : ZMod M) * (γ 1 1 : ZMod M) = 1 := by
    have h := congrArg (Int.castRingHom (ZMod M)) hd
    simpa only [Int.coe_castRingHom, Int.cast_sub, Int.cast_mul, Int.cast_one,
      hz, mul_zero, sub_zero] using h
  exact IsUnit.of_mul_eq_one_right _ he

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

/-- The literal common scalar, evaluated on the actual finite lattice test. -/
def cubicThetaFiniteScalar (D : WeilData (Fin 2) MpR MpF MpA)
    (M : ℕ) [NeZero M] (γ : SL(2, ℤ)) : ℂ :=
  (D.finiteAction (eisensteinSymplectic (γ : SL(2, ℚ)))
    (latticeTestFunction (M : ℚ) (by exact_mod_cast (NeZero.ne M)))).val 0

/-- Exact finite scalar action, derived from the even-period congruence and
actual residue-coset transport. Weight invariance is the only weight input. -/
theorem cubicThetaFinite_residueTest_scalar
    (D : WeilData (Fin 2) MpR MpF MpA) (M : ℕ) [NeZero M]
    (heven : 2 ∣ M) (γ : SL(2, ℤ)) (hc : 6 * (M : ℤ) ^ 2 ∣ γ 1 0)
    (w : (Fin 2 → ZMod M) → ℂ)
    (hw : ∀ r, w (fun i => (γ 1 1 : ZMod M) * r i) = w r) :
    D.finiteAction (eisensteinSymplectic (γ : SL(2, ℚ))) (finiteResidueTest w) =
      cubicThetaFiniteScalar D M γ • finiteResidueTest w := by
  let m := D.finiteLift (eisensteinSymplectic (γ : SL(2, ℚ)))
  have hm : D.finite.project m = eisensteinFiniteSymplectic γ := D.finiteLift_covers _
  have hcontrol : finiteBaseLatticeControl (M : ℚ) (by exact_mod_cast (NeZero.ne M))
      (D.finite.project m) := by
    rw [hm]
    exact eisensteinFiniteSymplectic_baseLatticeControl_nat M heven γ hc
  have hcos (r : Fin 2 → ZMod M) :
      D.finiteAction (eisensteinSymplectic (γ : SL(2, ℚ)))
        (latticeCosetTest (M : ℚ) (by exact_mod_cast (NeZero.ne M)) (residuePoint r)) =
      cubicThetaFiniteScalar D M γ • latticeCosetTest (M : ℚ)
        (by exact_mod_cast (NeZero.ne M))
        (residuePoint (fun i => (γ 1 1 : ZMod M) * r i)) := by
    obtain ⟨hp, hq, hphase⟩ := eisensteinFiniteSymplectic_residue_coset_conditions M γ r
    have h := finiteWeil_latticeCoset_action D (M : ℚ)
      (by exact_mod_cast (NeZero.ne M)) m hcontrol (residuePoint r)
      (residuePoint (fun i => (γ 1 1 : ZMod M) * r i))
    rw [hm] at h
    exact h hp hq hphase
  have hM : (M : ℤ) ∣ γ 1 0 := (dvd_mul_of_dvd_right (dvd_pow_self (M : ℤ) (by decide : 2 ≠ 0)) 6).trans hc
  let u : (ZMod M)ˣ := (cubicTheta_lowerRight_zmod_isUnit M γ hM).unit
  let e : (Fin 2 → ZMod M) ≃ (Fin 2 → ZMod M) := Equiv.piCongrRight (fun _ => u.mulLeft)
  have he (r : Fin 2 → ZMod M) : e r = (fun i => (γ 1 1 : ZMod M) * r i) := by
    funext i
    exact congrArg (fun d : ZMod M => d * r i)
      (cubicTheta_lowerRight_zmod_isUnit M γ hM).unit_spec
  unfold finiteResidueTest
  rw [map_sum, Finset.smul_sum]
  have hr := e.bijective.sum_comp (fun r : Fin 2 → ZMod M =>
    w r • (cubicThetaFiniteScalar D M γ • latticeCosetTest (M : ℚ)
      (by exact_mod_cast (NeZero.ne M)) (residuePoint r)))
  calc
    _ = ∑ r : Fin 2 → ZMod M, w (e r) •
        (cubicThetaFiniteScalar D M γ • latticeCosetTest (M : ℚ)
          (by exact_mod_cast (NeZero.ne M)) (residuePoint (e r))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [map_smul, hcos, he, hw]
    _ = _ := hr
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [smul_smul, smul_smul, mul_comm]

end ArtinMatthews
