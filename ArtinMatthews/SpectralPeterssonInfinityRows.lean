module

public import ArtinMatthews.SpectralPeterssonLiftedKloosterman
public import ArtinMatthews.SpectralCuspPeriodKloosterman
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Common-period matrices with the left cusp at infinity, with both diagonal lifts retained. -/

noncomputable section
open Matrix
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

theorem gamma0CuspCorrespondence_leftInfinity_iff (N : ℕ) (b M : SL(2, ℤ)) :
    M ∈ gamma0CuspCorrespondence N b 1 ↔
      (N : ℤ) ∣ M 1 0 * b 0 0 + M 1 1 * b 1 0 := by
  change (1 : SL(2, ℤ))⁻¹ * M * b ∈ CongruenceSubgroup.Gamma0 N ↔ _
  rw [inv_one, one_mul, CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (N : ℤ) ∣ ((M : Matrix (Fin 2) (Fin 2) ℤ) * (b : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 ↔ _
  rw [Matrix.mul_apply, Fin.sum_univ_two]

private theorem residueLift_cast {N c : ℕ} [NeZero c] (d : ZMod c) (j : Fin N) :
    (peterssonResidueLift d j : ZMod c) = d := by
  simp [peterssonResidueLift]

private theorem residueLift_nonneg {N c : ℕ} (d : ZMod c) (j : Fin N) :
    0 ≤ peterssonResidueLift d j := by
  unfold peterssonResidueLift
  positivity

private theorem residueLift_lt {N c : ℕ} [NeZero c] (d : ZMod c) (j : Fin N) :
    peterssonResidueLift d j < (N : ℤ) * c := by
  have h := (finProdFinEquiv (j, (⟨d.val, ZMod.val_lt d⟩ : Fin c))).isLt
  change d.val + c * j.val < N * c at h
  unfold peterssonResidueLift
  exact_mod_cast h

private theorem residueLift_injective (N c : ℕ) [NeZero c] :
    Function.Injective (fun p : ZMod c × Fin N => peterssonResidueLift p.1 p.2) := by
  rintro ⟨d,j⟩ ⟨e,k⟩ h
  change peterssonResidueLift d j = peterssonResidueLift e k at h
  have hde := congrArg (fun z : ℤ => (z : ZMod c)) h
  simp only [residueLift_cast] at hde
  subst e
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hmul : (c : ℤ) * j.val = (c : ℤ) * k.val := add_left_cancel h
  have hval := mul_left_cancel₀ hc hmul
  exact Prod.ext rfl (Fin.ext (by exact_mod_cast hval))

private theorem exists_residueLift (N c : ℕ) [NeZero c] (x : ℤ) (hx : 0 ≤ x)
    (hlt : x < (N : ℤ) * c) : ∃ (d : ZMod c) (j : Fin N), peterssonResidueLift d j = x := by
  have hnat : x.toNat < N * c := by
    have h : (x.toNat : ℤ) < ((N * c : ℕ) : ℤ) := by
      simpa only [Int.toNat_of_nonneg hx, Nat.cast_mul] using hlt
    exact_mod_cast h
  obtain ⟨⟨j,d⟩,heq⟩ :=
    (finProdFinEquiv : Fin N × Fin c ≃ Fin (N * c)).surjective ⟨x.toNat, hnat⟩
  have hval := congrArg Fin.val heq
  change d.val + c * j.val = x.toNat at hval
  refine ⟨(d.val : ZMod c), j, ?_⟩
  rw [peterssonResidueLift, ZMod.val_natCast_of_lt d.isLt]
  have h := congrArg (fun n : ℕ => (n : ℤ)) hval
  simpa only [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hx] using h

/-- The right diagonal lift satisfying the literal lower-left congruence. -/
def peterssonMaskedRightLift (N : ℕ) (b : SL(2, ℤ)) (c : ℕ) :=
  {p : (ZMod c)ˣ × Fin N // (N : ℤ) ∣ (c : ℤ) * b 0 0 + peterssonResidueLift p.1.val p.2 * b 1 0}

instance (N : ℕ) (b : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Fintype (peterssonMaskedRightLift N b c) := by
  unfold peterssonMaskedRightLift
  exact Fintype.ofFinite _

/-- A determinant-one matrix from a masked right lift and a free left lift. -/
def peterssonInfinityReducedMatrix (N : ℕ) (b : SL(2, ℤ)) (c : ℕ) [NeZero c]
    (p : peterssonMaskedRightLift N b c × Fin N) : gamma0CuspReducedMatrix N b 1 c := by
  let A := peterssonResidueLift (p.1.val.1⁻¹).val p.2
  let D := peterssonResidueLift p.1.val.1.val p.1.val.2
  have hdvd : (c : ℤ) ∣ A * D - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    dsimp only [A,D]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, residueLift_cast, Units.inv_mul, sub_self]
  let M : SL(2, ℤ) := ⟨!![A, (A * D - 1) / (c : ℤ); (c : ℤ), D], by
    rw [Matrix.det_fin_two]
    change A * D - ((A * D - 1) / (c : ℤ)) * c = 1
    rw [Int.ediv_mul_cancel hdvd]
    ring⟩
  exact ⟨M, (gamma0CuspCorrespondence_leftInfinity_iff N b M).2 p.1.property, rfl,
    residueLift_nonneg _ _, residueLift_lt _ _, residueLift_nonneg _ _, residueLift_lt _ _⟩

private theorem infinityReducedMatrix_injective (N : ℕ) (b : SL(2, ℤ))
    (c : ℕ) [NeZero c] : Function.Injective (peterssonInfinityReducedMatrix N b c) := by
  intro p q hpq
  have hA := congrArg (fun R : gamma0CuspReducedMatrix N b 1 c => R.val 0 0) hpq
  have hD := congrArg (fun R : gamma0CuspReducedMatrix N b 1 c => R.val 1 1) hpq
  change peterssonResidueLift (p.1.val.1⁻¹).val p.2 =
    peterssonResidueLift (q.1.val.1⁻¹).val q.2 at hA
  change peterssonResidueLift p.1.val.1.val p.1.val.2 =
    peterssonResidueLift q.1.val.1.val q.1.val.2 at hD
  have ha : ((p.1.val.1⁻¹).val,p.2) = ((q.1.val.1⁻¹).val,q.2) := residueLift_injective N c hA
  have hd : (p.1.val.1.val,p.1.val.2) = (q.1.val.1.val,q.1.val.2) := residueLift_injective N c hD
  have hu : p.1.val.1 = q.1.val.1 := Units.ext (congrArg (fun x : ZMod c × Fin N => x.1) hd)
  have hj : p.1.val.2 = q.1.val.2 := congrArg (fun x : ZMod c × Fin N => x.2) hd
  have hi : p.2 = q.2 := congrArg (fun x : ZMod c × Fin N => x.2) ha
  exact Prod.ext (Subtype.ext (Prod.ext hu hj)) hi

private theorem infinityReducedMatrix_surjective (N : ℕ) (b : SL(2, ℤ))
    (c : ℕ) [NeZero c] : Function.Surjective (peterssonInfinityReducedMatrix N b c) := by
  intro R
  have hdet : R.val 0 0 * R.val 1 1 - R.val 0 1 * (c : ℤ) = 1 := by
    simpa only [Matrix.det_fin_two, R.property.2.1] using R.val.prop
  have hmod : (R.val 0 0 : ZMod c) * (R.val 1 1 : ZMod c) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod c)) hdet
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, sub_zero, Int.cast_one] using h
  obtain ⟨d,j,hD⟩ := exists_residueLift N c _ R.property.2.2.2.2.1 R.property.2.2.2.2.2
  obtain ⟨a,i,hA⟩ := exists_residueLift N c _ R.property.2.2.1 R.property.2.2.2.1
  let u : (ZMod c)ˣ := ⟨(R.val 1 1 : ZMod c), (R.val 0 0 : ZMod c), by
    rw [mul_comm]
    exact hmod, hmod⟩
  have hu : u.val = d := by
    change (R.val 1 1 : ZMod c) = d
    rw [← hD, residueLift_cast]
  have hv : (u⁻¹).val = a := by
    change (R.val 0 0 : ZMod c) = a
    rw [← hA, residueLift_cast]
  let p : peterssonMaskedRightLift N b c := ⟨(u,j), by
    change (N : ℤ) ∣ (c : ℤ) * b 0 0 + peterssonResidueLift u.val j * b 1 0
    rw [hu, hD]
    simpa only [R.property.2.1] using
      (gamma0CuspCorrespondence_leftInfinity_iff N b R.val).1 R.property.1⟩
  refine ⟨(p,i), Subtype.ext ?_⟩
  refine specialLinear_eq_of_diagonal_lower (c := (c : ℤ)) (by exact_mod_cast NeZero.ne c)
    _ R.val rfl R.property.2.1 ?_ ?_
  · change peterssonResidueLift (u⁻¹).val i = R.val 0 0
    rwa [hv]
  · change peterssonResidueLift u.val j = R.val 1 1
    rwa [hu]

def peterssonInfinityReducedMatrixEquiv (N : ℕ) (b : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    peterssonMaskedRightLift N b c × Fin N ≃ gamma0CuspReducedMatrix N b 1 c :=
  Equiv.ofBijective (peterssonInfinityReducedMatrix N b c)
    ⟨infinityReducedMatrix_injective N b c, infinityReducedMatrix_surjective N b c⟩

theorem gamma0PeriodKloostermanSum_leftInfinity_lifted (N : ℕ) [NeZero N]
    (b : SL(2, ℤ)) (c : ℕ) [NeZero c] (h m : ℤ) :
    gamma0PeriodKloostermanSum N b 1 c h ((N : ℤ) * m) =
      (N : ℂ) * peterssonLiftedKloostermanSum N c (b 0 0) (b 1 0) h m := by
  classical
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne c
  let f (p : (ZMod c)ˣ × Fin N) : ℂ :=
    atkinPhase ((h : ℝ) * (peterssonResidueLift p.1.val p.2 : ℝ) / ((N : ℝ) * c) +
      (m : ℝ) * (p.1⁻¹).val.val / c)
  have hphase (p : peterssonMaskedRightLift N b c) (i : Fin N) :
      cuspGeometricPhase N h ((N : ℤ) * m) c
        (peterssonInfinityReducedMatrix N b c (p,i)).val = f p.val := by
    have he :
        ((h : ℝ) * (peterssonResidueLift p.val.1.val p.val.2 : ℝ) +
          ((N : ℤ) * m : ℤ) * (peterssonResidueLift (p.val.1⁻¹).val i : ℝ)) /
            ((N : ℝ) * c) =
        (h : ℝ) * (peterssonResidueLift p.val.1.val p.val.2 : ℝ) / ((N : ℝ) * c) +
          (m : ℝ) * (p.val.1⁻¹).val.val / c + ((m * i.val : ℤ) : ℝ) := by
      unfold peterssonResidueLift
      push_cast
      field_simp [hN,hc]
      ring
    change atkinPhase (((h : ℝ) * (peterssonResidueLift p.val.1.val p.val.2 : ℝ) +
      ((N : ℤ) * m : ℤ) * (peterssonResidueLift (p.val.1⁻¹).val i : ℝ)) /
        ((N : ℝ) * c)) = f p.val
    rw [he, atkinPhase_add, atkinPhase_int, mul_one]
  unfold gamma0PeriodKloostermanSum
  rw [← (peterssonInfinityReducedMatrixEquiv N b c).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ p : peterssonMaskedRightLift N b c, ∑ i : Fin N,
    cuspGeometricPhase N h ((N : ℤ) * m) c (peterssonInfinityReducedMatrix N b c (p,i)).val) = _
  simp_rw [hphase, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  congr 1
  calc
    (∑ p : peterssonMaskedRightLift N b c, f p.val) =
      ∑ p ∈ Finset.univ.filter
        (fun p : (ZMod c)ˣ × Fin N => (N : ℤ) ∣ (c : ℤ) * b 0 0 + peterssonResidueLift p.1.val p.2 * b 1 0),
        f p :=
      (Finset.sum_subtype _ (fun _ => Finset.mem_filter.trans (by simp)) f).symm
    _ = _ := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      rfl

end ArtinMatthews
