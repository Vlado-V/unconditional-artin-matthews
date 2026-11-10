module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! The determinant definition of the norm preserves a principal
congruence. This supplies the actual conductor input for norm pullback. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [Module.Free R B] [Module.Finite R B]

theorem norm_one_add_multiple_sub_one_dvd (r : R) (b : B) :
    r ∣ Algebra.norm R (1 + algebraMap R B r * b) - 1 := by
  let basis := Module.Free.chooseBasis R B
  let f := Ideal.Quotient.mk (Ideal.span {r})
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub,map_one,Algebra.norm_eq_matrix_det basis]
  have hfr : f r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self r)
  have hscalar : f.mapMatrix (algebraMap R (Matrix (Module.Free.ChooseBasisIndex R B)
      (Module.Free.ChooseBasisIndex R B) R) r) = 0 := by
    ext i j
    change f (if i=j then r else 0) = 0
    split_ifs
    · exact hfr
    · exact map_zero f
  have hm : f.mapMatrix (Algebra.leftMulMatrix basis (1 + algebraMap R B r * b)) = 1 := by
    rw [map_add,map_one,map_mul,AlgHom.commutes,map_add,map_one,map_mul,hscalar,zero_mul,add_zero]
  rw [RingHom.map_det]
  change (f.mapMatrix (Algebra.leftMulMatrix basis (1 + algebraMap R B r * b))).det - 1 = 0
  rw [hm,Matrix.det_one,sub_self]

theorem norm_sub_one_dvd_of_sub_one_dvd (r : R) (a : B)
    (ha : algebraMap R B r ∣ a-1) : r ∣ Algebra.norm R a-1 := by
  obtain ⟨b,hb⟩ := ha
  have he : a = 1 + algebraMap R B r * b := by linear_combination hb
  rw [he]
  exact norm_one_add_multiple_sub_one_dvd r b

end
end ArtinMatthews
