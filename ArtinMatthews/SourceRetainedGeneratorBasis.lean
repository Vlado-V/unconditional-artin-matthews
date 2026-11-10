module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus


set_option backward.privateInPublic true
@[expose] public section

/-! A basis selected from the original generators, with its coordinate
maps on the span and linear extensions to the ambient space. -/
namespace ArtinMatthews

open scoped BigOperators

noncomputable section

variable {G W : Type*} [AddCommGroup W] [Module ℂ W]

def sourceRetainedGenerator (v : G → W) (x : G) : Submodule.span ℂ (Set.range v) :=
  ⟨v x, Submodule.subset_span (Set.mem_range_self x)⟩

theorem sourceRetainedGenerator_span (v : G → W) :
    Submodule.span ℂ (Set.range (sourceRetainedGenerator v)) = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp w.property
  rw [← Finsupp.range_linearCombination ℂ (v := sourceRetainedGenerator v)]
  refine ⟨c, Subtype.ext ?_⟩
  exact (Finsupp.apply_linearCombination ℂ (Submodule.span ℂ (Set.range v)).subtype
    (sourceRetainedGenerator v) c).trans hc

variable [FiniteDimensional ℂ W]

def sourceRetainedBasis (v : G → W) :
    Module.Basis (Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v))))
      ℂ (Submodule.span ℂ (Set.range v)) :=
  let b := Module.Basis.ofSpan (sourceRetainedGenerator_span v).ge
  b.reindex (b.indexEquiv (Module.finBasis ℂ (Submodule.span ℂ (Set.range v))))

theorem sourceRetainedBasis_mem_range (v : G → W)
    (k : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v)))) :
    sourceRetainedBasis v k ∈ Set.range (sourceRetainedGenerator v) := by
  simp only [sourceRetainedBasis, Module.Basis.reindex_apply]
  exact Module.Basis.ofSpan_subset _ (Set.mem_range_self _)

def sourceRetainedBasisLift (v : G → W)
    (k : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v)))) : G :=
  Classical.choose (sourceRetainedBasis_mem_range v k)

theorem sourceRetainedBasisLift_spec (v : G → W)
    (k : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v)))) :
    sourceRetainedGenerator v (sourceRetainedBasisLift v k) = sourceRetainedBasis v k :=
  Classical.choose_spec (sourceRetainedBasis_mem_range v k)

def sourceRetainedSpanCoordinate (v : G → W)
    (k : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v)))) :
    Submodule.span ℂ (Set.range v) →ₗ[ℂ] ℂ :=
  (sourceRetainedBasis v).coord k

def sourceRetainedCoordinate (v : G → W)
    (k : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v)))) : W →ₗ[ℂ] ℂ :=
  Classical.choose (sourceRetainedSpanCoordinate v k).exists_extend

theorem sourceRetainedCoordinate_on_span (v : G → W)
    (k : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v))))
    (w : Submodule.span ℂ (Set.range v)) :
    sourceRetainedCoordinate v k (w : W) = sourceRetainedSpanCoordinate v k w :=
  DFunLike.congr_fun (Classical.choose_spec (sourceRetainedSpanCoordinate v k).exists_extend) w

theorem sourceRetainedCoordinate_on_generator (v : G → W)
    (k : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v)))) (x : G) :
    sourceRetainedCoordinate v k (v x) =
      (sourceRetainedBasis v).repr (sourceRetainedGenerator v x) k :=
  sourceRetainedCoordinate_on_span v k (sourceRetainedGenerator v x)

theorem sourceRetainedCoordinate_on_basisLift (v : G → W)
    (j k : Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range v)))) :
    sourceRetainedCoordinate v j (v (sourceRetainedBasisLift v k)) =
      if j = k then 1 else 0 := by
  rw [sourceRetainedCoordinate_on_generator, sourceRetainedBasisLift_spec, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

theorem sourceRetainedSlice_expansion (v : G → W) (a : G → ℂ)
    (hrel : ∀ c : G →₀ ℂ,
      c.sum (fun x z => z • v x) = 0 → c.sum (fun x z => z * a x) = 0)
    (x : G) :
    a x = ∑ k, a (sourceRetainedBasisLift v k) * sourceRetainedCoordinate v k (v x) := by
  let L := Finsupp.linearCombination ℂ (sourceRetainedGenerator v)
  let T := Finsupp.linearCombination ℂ a
  have hL : Function.Surjective L :=
    LinearMap.range_eq_top.mp ((Finsupp.range_linearCombination ℂ
      (v := sourceRetainedGenerator v)).trans (sourceRetainedGenerator_span v))
  have hker : LinearMap.ker L ≤ LinearMap.ker T := by
    intro c hc
    apply LinearMap.mem_ker.mpr
    have hv : Finsupp.linearCombination ℂ v c = 0 := by
      calc
        _ = (Submodule.span ℂ (Set.range v)).subtype (L c) :=
          (Finsupp.apply_linearCombination ℂ (Submodule.span ℂ (Set.range v)).subtype
            (sourceRetainedGenerator v) c).symm
        _ = 0 := by rw [LinearMap.mem_ker.mp hc, map_zero]
    simpa only [T, Finsupp.linearCombination_apply, smul_eq_mul] using hrel c hv
  let f := L.liftOfSurjective hL ⟨T,hker⟩
  have hEval (y : G) : f (sourceRetainedGenerator v y) = a y := by
    simpa only [L, T, Finsupp.linearCombination_single, one_smul] using
      (LinearMap.equivOfSurjective_apply (f := L) hL hker (m := Finsupp.single y 1))
  have hsum : (∑ k, sourceRetainedCoordinate v k (v x) •
      sourceRetainedGenerator v (sourceRetainedBasisLift v k)) = sourceRetainedGenerator v x := by
    simpa only [sourceRetainedCoordinate_on_generator, sourceRetainedBasisLift_spec] using
      (sourceRetainedBasis v).sum_repr (sourceRetainedGenerator v x)
  calc
    a x = f (sourceRetainedGenerator v x) := (hEval x).symm
    _ = f (∑ k, sourceRetainedCoordinate v k (v x) •
        sourceRetainedGenerator v (sourceRetainedBasisLift v k)) := congrArg f hsum.symm
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul, hEval, smul_eq_mul, mul_comm]

end
end ArtinMatthews
