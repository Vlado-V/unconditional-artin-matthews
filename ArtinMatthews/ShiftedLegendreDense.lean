module

public import ArtinMatthews.ShiftedLegendreIntervalLp
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass


set_option backward.privateInPublic true
@[expose] public section

/-! The shifted Legendre polynomials span a dense subspace of the interval mass space. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal Polynomial Topology unitInterval
noncomputable section

def shiftedLegendreCoordinate : C(I, ℂ) :=
  ⟨fun x => (x.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

def shiftedLegendreEval : ℂ[X] →ₐ[ℂ] C(I, ℂ) :=
  Polynomial.aeval shiftedLegendreCoordinate

theorem shiftedLegendreEval_apply (p : ℂ[X]) (x : I) :
    shiftedLegendreEval p x = Polynomial.aeval (x.val : ℂ) p :=
  (Polynomial.aeval_algHom_apply (ContinuousMap.evalAlgHom ℂ ℂ x)
    shiftedLegendreCoordinate p).symm

def shiftedLegendreComplexSequence : Polynomial.Sequence ℂ where
  elems' n := (Polynomial.shiftedLegendre n).map (Int.castRingHom ℂ)
  degree_eq' n := by
    rw [Polynomial.degree_map_eq_of_injective Int.cast_injective, Polynomial.degree_shiftedLegendre]

theorem shiftedLegendreEval_sequence (n : ℕ) :
    shiftedLegendreEval (shiftedLegendreComplexSequence n) = shiftedLegendreContinuous n := by
  ext x
  rw [shiftedLegendreEval_apply, shiftedLegendreContinuous_apply]
  exact (Polynomial.map_aeval_eq_aeval_map (φ := Int.castRingHom ℂ)
    (ψ := Complex.ofRealHom) (Subsingleton.elim _ _) (Polynomial.shiftedLegendre n) x.val).symm

theorem shiftedLegendreComplexSequence_span :
    Submodule.span ℂ (range shiftedLegendreComplexSequence) = ⊤ :=
  shiftedLegendreComplexSequence.span fun n =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (shiftedLegendreComplexSequence.ne_zero n))

theorem shiftedLegendreEval_denseRange : DenseRange shiftedLegendreEval := by
  let A := StarAlgebra.adjoin ℂ ({shiftedLegendreCoordinate} : Set C(I, ℂ))
  have hstar : star shiftedLegendreCoordinate = shiftedLegendreCoordinate := by
    ext x
    simp [shiftedLegendreCoordinate, ContinuousMap.star_apply, Complex.star_def]
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    exact ⟨_, ⟨shiftedLegendreCoordinate, StarAlgebra.self_mem_adjoin_singleton ℂ _, rfl⟩,
      fun h => hxy (Subtype.ext (Complex.ofReal_injective h))⟩
  have hA : A.toSubalgebra = shiftedLegendreEval.range := by
    change (StarAlgebra.adjoin ℂ ({shiftedLegendreCoordinate} : Set C(I, ℂ))).toSubalgebra = _
    rw [StarAlgebra.adjoin_toSubalgebra, Set.star_singleton, hstar, Set.union_self,
      Algebra.adjoin_singleton_eq_range_aeval]
    rfl
  have hrange : (A : Set C(I, ℂ)) = range shiftedLegendreEval := by
    change (A.toSubalgebra : Set C(I, ℂ)) = _
    rw [hA]
    rfl
  apply dense_iff_closure_eq.mpr
  rw [← hrange, ← StarSubalgebra.topologicalClosure_coe,
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep]
  rfl

theorem shiftedLegendreVector_dense_span :
    (Submodule.span ℂ (range shiftedLegendreVector)).topologicalClosure = ⊤ := by
  let Q : ℂ[X] →ₗ[ℂ] ShiftedLegendreL2 :=
    shiftedLegendreToLp.toLinearMap.comp shiftedLegendreEval.toLinearMap
  have hLp : DenseRange shiftedLegendreToLp :=
    ContinuousMap.toLp_denseRange (α := I) (p := (2 : ℝ≥0∞)) (E := ℂ)
      (𝕜 := ℂ) (μ := (volume : Measure I)) (by norm_num)
  have hd : DenseRange Q :=
    hLp.comp shiftedLegendreEval_denseRange shiftedLegendreToLp.continuous
  have hRange : LinearMap.range Q = Submodule.span ℂ (range shiftedLegendreVector) := by
    rw [← Submodule.map_top, ← shiftedLegendreComplexSequence_span, Submodule.map_span]
    apply congrArg (Submodule.span ℂ)
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext n
    change shiftedLegendreToLp (shiftedLegendreEval (shiftedLegendreComplexSequence n)) =
      shiftedLegendreToLp (shiftedLegendreContinuous n)
    rw [shiftedLegendreEval_sequence]
  apply SetLike.ext'
  change closure (Submodule.span ℂ (range shiftedLegendreVector) : Set ShiftedLegendreL2) = univ
  rw [← hRange]
  exact hd.closure_range

end
end ArtinMatthews
